%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:00 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 111 expanded)
%              Number of leaves         :   37 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  145 ( 240 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_20,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_42,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_95,plain,(
    ! [A_50] :
      ( v1_xboole_0(A_50)
      | r2_hidden('#skF_1'(A_50),A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_102,plain,(
    ! [A_50] :
      ( m1_subset_1('#skF_1'(A_50),A_50)
      | v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_95,c_16])).

tff(c_120,plain,(
    ! [A_58,B_59] :
      ( k6_domain_1(A_58,B_59) = k1_tarski(B_59)
      | ~ m1_subset_1(B_59,A_58)
      | v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_127,plain,(
    ! [A_50] :
      ( k6_domain_1(A_50,'#skF_1'(A_50)) = k1_tarski('#skF_1'(A_50))
      | v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_102,c_120])).

tff(c_233,plain,(
    ! [A_75,B_76] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_75),B_76),A_75)
      | ~ m1_subset_1(B_76,u1_struct_0(A_75))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1611,plain,(
    ! [A_148] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_148))),A_148)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_148)),u1_struct_0(A_148))
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148)
      | v2_struct_0(A_148)
      | v1_xboole_0(u1_struct_0(A_148)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_233])).

tff(c_46,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,(
    ! [A_37] :
      ( k1_xboole_0 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_54])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66,plain,(
    ! [A_6] : k2_xboole_0(A_6,'#skF_4') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_8])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),B_9) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_88,plain,(
    ! [A_45,B_46] : k2_xboole_0(k1_tarski(A_45),B_46) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_12])).

tff(c_92,plain,(
    ! [A_45] : k1_tarski(A_45) != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_88])).

tff(c_138,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(k6_domain_1(A_61,B_62),k1_zfmisc_1(A_61))
      | ~ m1_subset_1(B_62,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_146,plain,(
    ! [A_50] :
      ( m1_subset_1(k1_tarski('#skF_1'(A_50)),k1_zfmisc_1(A_50))
      | ~ m1_subset_1('#skF_1'(A_50),A_50)
      | v1_xboole_0(A_50)
      | v1_xboole_0(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_138])).

tff(c_14,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_77,plain,(
    ! [A_10] : m1_subset_1('#skF_4',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_14])).

tff(c_10,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_60,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_10])).

tff(c_527,plain,(
    ! [C_99,B_100,A_101] :
      ( C_99 = B_100
      | ~ r1_tarski(B_100,C_99)
      | ~ v2_tex_2(C_99,A_101)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ v3_tex_2(B_100,A_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_529,plain,(
    ! [A_7,A_101] :
      ( A_7 = '#skF_4'
      | ~ v2_tex_2(A_7,A_101)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ v3_tex_2('#skF_4',A_101)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(resolution,[status(thm)],[c_60,c_527])).

tff(c_773,plain,(
    ! [A_111,A_112] :
      ( A_111 = '#skF_4'
      | ~ v2_tex_2(A_111,A_112)
      | ~ m1_subset_1(A_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ v3_tex_2('#skF_4',A_112)
      | ~ l1_pre_topc(A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_529])).

tff(c_788,plain,(
    ! [A_112] :
      ( k1_tarski('#skF_1'(u1_struct_0(A_112))) = '#skF_4'
      | ~ v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_112))),A_112)
      | ~ v3_tex_2('#skF_4',A_112)
      | ~ l1_pre_topc(A_112)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_112)),u1_struct_0(A_112))
      | v1_xboole_0(u1_struct_0(A_112)) ) ),
    inference(resolution,[status(thm)],[c_146,c_773])).

tff(c_810,plain,(
    ! [A_112] :
      ( ~ v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_112))),A_112)
      | ~ v3_tex_2('#skF_4',A_112)
      | ~ l1_pre_topc(A_112)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_112)),u1_struct_0(A_112))
      | v1_xboole_0(u1_struct_0(A_112)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_788])).

tff(c_1616,plain,(
    ! [A_149] :
      ( ~ v3_tex_2('#skF_4',A_149)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_149)),u1_struct_0(A_149))
      | ~ l1_pre_topc(A_149)
      | ~ v2_pre_topc(A_149)
      | v2_struct_0(A_149)
      | v1_xboole_0(u1_struct_0(A_149)) ) ),
    inference(resolution,[status(thm)],[c_1611,c_810])).

tff(c_1657,plain,(
    ! [A_152] :
      ( ~ v3_tex_2('#skF_4',A_152)
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152)
      | v1_xboole_0(u1_struct_0(A_152)) ) ),
    inference(resolution,[status(thm)],[c_102,c_1616])).

tff(c_22,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1666,plain,(
    ! [A_153] :
      ( ~ l1_struct_0(A_153)
      | ~ v3_tex_2('#skF_4',A_153)
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_1657,c_22])).

tff(c_1672,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1666])).

tff(c_1676,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1672])).

tff(c_1677,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1676])).

tff(c_1680,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1677])).

tff(c_1684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1680])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.81/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.68  
% 3.81/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.68  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.81/1.68  
% 3.81/1.68  %Foreground sorts:
% 3.81/1.68  
% 3.81/1.68  
% 3.81/1.68  %Background operators:
% 3.81/1.68  
% 3.81/1.68  
% 3.81/1.68  %Foreground operators:
% 3.81/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.81/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.81/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.81/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.81/1.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.81/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.81/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.81/1.68  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.81/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.81/1.68  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.81/1.68  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.81/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.81/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.81/1.68  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.81/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.81/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.81/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.81/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.81/1.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.81/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.81/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.81/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.81/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.81/1.68  
% 4.15/1.70  tff(f_126, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 4.15/1.70  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.15/1.70  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.15/1.70  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 4.15/1.70  tff(f_80, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.15/1.70  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 4.15/1.70  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.15/1.70  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.15/1.70  tff(f_42, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.15/1.70  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.15/1.70  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.15/1.70  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.15/1.70  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 4.15/1.70  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.15/1.70  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.15/1.70  tff(c_20, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.15/1.70  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.15/1.70  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.15/1.70  tff(c_42, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.15/1.70  tff(c_95, plain, (![A_50]: (v1_xboole_0(A_50) | r2_hidden('#skF_1'(A_50), A_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.15/1.70  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.15/1.70  tff(c_102, plain, (![A_50]: (m1_subset_1('#skF_1'(A_50), A_50) | v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_95, c_16])).
% 4.15/1.70  tff(c_120, plain, (![A_58, B_59]: (k6_domain_1(A_58, B_59)=k1_tarski(B_59) | ~m1_subset_1(B_59, A_58) | v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.15/1.70  tff(c_127, plain, (![A_50]: (k6_domain_1(A_50, '#skF_1'(A_50))=k1_tarski('#skF_1'(A_50)) | v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_102, c_120])).
% 4.15/1.70  tff(c_233, plain, (![A_75, B_76]: (v2_tex_2(k6_domain_1(u1_struct_0(A_75), B_76), A_75) | ~m1_subset_1(B_76, u1_struct_0(A_75)) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.15/1.70  tff(c_1611, plain, (![A_148]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_148))), A_148) | ~m1_subset_1('#skF_1'(u1_struct_0(A_148)), u1_struct_0(A_148)) | ~l1_pre_topc(A_148) | ~v2_pre_topc(A_148) | v2_struct_0(A_148) | v1_xboole_0(u1_struct_0(A_148)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_233])).
% 4.15/1.70  tff(c_46, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.15/1.70  tff(c_54, plain, (![A_37]: (k1_xboole_0=A_37 | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.15/1.70  tff(c_58, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_46, c_54])).
% 4.15/1.70  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.15/1.70  tff(c_66, plain, (![A_6]: (k2_xboole_0(A_6, '#skF_4')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_8])).
% 4.15/1.70  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.15/1.70  tff(c_88, plain, (![A_45, B_46]: (k2_xboole_0(k1_tarski(A_45), B_46)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_12])).
% 4.15/1.70  tff(c_92, plain, (![A_45]: (k1_tarski(A_45)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_66, c_88])).
% 4.15/1.70  tff(c_138, plain, (![A_61, B_62]: (m1_subset_1(k6_domain_1(A_61, B_62), k1_zfmisc_1(A_61)) | ~m1_subset_1(B_62, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.15/1.70  tff(c_146, plain, (![A_50]: (m1_subset_1(k1_tarski('#skF_1'(A_50)), k1_zfmisc_1(A_50)) | ~m1_subset_1('#skF_1'(A_50), A_50) | v1_xboole_0(A_50) | v1_xboole_0(A_50))), inference(superposition, [status(thm), theory('equality')], [c_127, c_138])).
% 4.15/1.70  tff(c_14, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.15/1.70  tff(c_77, plain, (![A_10]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_14])).
% 4.15/1.70  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.15/1.70  tff(c_60, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_10])).
% 4.15/1.70  tff(c_527, plain, (![C_99, B_100, A_101]: (C_99=B_100 | ~r1_tarski(B_100, C_99) | ~v2_tex_2(C_99, A_101) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(A_101))) | ~v3_tex_2(B_100, A_101) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.15/1.70  tff(c_529, plain, (![A_7, A_101]: (A_7='#skF_4' | ~v2_tex_2(A_7, A_101) | ~m1_subset_1(A_7, k1_zfmisc_1(u1_struct_0(A_101))) | ~v3_tex_2('#skF_4', A_101) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(resolution, [status(thm)], [c_60, c_527])).
% 4.15/1.70  tff(c_773, plain, (![A_111, A_112]: (A_111='#skF_4' | ~v2_tex_2(A_111, A_112) | ~m1_subset_1(A_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~v3_tex_2('#skF_4', A_112) | ~l1_pre_topc(A_112))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_529])).
% 4.15/1.70  tff(c_788, plain, (![A_112]: (k1_tarski('#skF_1'(u1_struct_0(A_112)))='#skF_4' | ~v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_112))), A_112) | ~v3_tex_2('#skF_4', A_112) | ~l1_pre_topc(A_112) | ~m1_subset_1('#skF_1'(u1_struct_0(A_112)), u1_struct_0(A_112)) | v1_xboole_0(u1_struct_0(A_112)))), inference(resolution, [status(thm)], [c_146, c_773])).
% 4.15/1.70  tff(c_810, plain, (![A_112]: (~v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_112))), A_112) | ~v3_tex_2('#skF_4', A_112) | ~l1_pre_topc(A_112) | ~m1_subset_1('#skF_1'(u1_struct_0(A_112)), u1_struct_0(A_112)) | v1_xboole_0(u1_struct_0(A_112)))), inference(negUnitSimplification, [status(thm)], [c_92, c_788])).
% 4.15/1.70  tff(c_1616, plain, (![A_149]: (~v3_tex_2('#skF_4', A_149) | ~m1_subset_1('#skF_1'(u1_struct_0(A_149)), u1_struct_0(A_149)) | ~l1_pre_topc(A_149) | ~v2_pre_topc(A_149) | v2_struct_0(A_149) | v1_xboole_0(u1_struct_0(A_149)))), inference(resolution, [status(thm)], [c_1611, c_810])).
% 4.15/1.70  tff(c_1657, plain, (![A_152]: (~v3_tex_2('#skF_4', A_152) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152) | v2_struct_0(A_152) | v1_xboole_0(u1_struct_0(A_152)))), inference(resolution, [status(thm)], [c_102, c_1616])).
% 4.15/1.70  tff(c_22, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.15/1.70  tff(c_1666, plain, (![A_153]: (~l1_struct_0(A_153) | ~v3_tex_2('#skF_4', A_153) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153))), inference(resolution, [status(thm)], [c_1657, c_22])).
% 4.15/1.70  tff(c_1672, plain, (~l1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_1666])).
% 4.15/1.70  tff(c_1676, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1672])).
% 4.15/1.70  tff(c_1677, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_1676])).
% 4.15/1.70  tff(c_1680, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_1677])).
% 4.15/1.70  tff(c_1684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1680])).
% 4.15/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.70  
% 4.15/1.70  Inference rules
% 4.15/1.70  ----------------------
% 4.15/1.70  #Ref     : 0
% 4.15/1.70  #Sup     : 350
% 4.15/1.70  #Fact    : 0
% 4.15/1.70  #Define  : 0
% 4.15/1.70  #Split   : 6
% 4.15/1.70  #Chain   : 0
% 4.15/1.70  #Close   : 0
% 4.15/1.70  
% 4.15/1.70  Ordering : KBO
% 4.15/1.70  
% 4.15/1.70  Simplification rules
% 4.15/1.70  ----------------------
% 4.15/1.70  #Subsume      : 23
% 4.15/1.70  #Demod        : 336
% 4.15/1.70  #Tautology    : 150
% 4.15/1.70  #SimpNegUnit  : 91
% 4.15/1.70  #BackRed      : 11
% 4.15/1.70  
% 4.15/1.70  #Partial instantiations: 0
% 4.15/1.70  #Strategies tried      : 1
% 4.15/1.70  
% 4.15/1.70  Timing (in seconds)
% 4.15/1.70  ----------------------
% 4.15/1.70  Preprocessing        : 0.32
% 4.15/1.71  Parsing              : 0.17
% 4.15/1.71  CNF conversion       : 0.02
% 4.15/1.71  Main loop            : 0.61
% 4.15/1.71  Inferencing          : 0.21
% 4.15/1.71  Reduction            : 0.19
% 4.15/1.71  Demodulation         : 0.13
% 4.15/1.71  BG Simplification    : 0.03
% 4.15/1.71  Subsumption          : 0.13
% 4.15/1.71  Abstraction          : 0.03
% 4.15/1.71  MUC search           : 0.00
% 4.15/1.71  Cooper               : 0.00
% 4.15/1.71  Total                : 0.97
% 4.15/1.71  Index Insertion      : 0.00
% 4.15/1.71  Index Deletion       : 0.00
% 4.15/1.71  Index Matching       : 0.00
% 4.15/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
