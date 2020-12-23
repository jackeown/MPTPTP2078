%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:01 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 105 expanded)
%              Number of leaves         :   37 (  51 expanded)
%              Depth                    :   16
%              Number of atoms          :  146 ( 225 expanded)
%              Number of equality atoms :   18 (  27 expanded)
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

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_107,axiom,(
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

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_95,axiom,(
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

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_22,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_42,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_95,plain,(
    ! [A_50] :
      ( v1_xboole_0(A_50)
      | r2_hidden('#skF_1'(A_50),A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_102,plain,(
    ! [A_50] :
      ( m1_subset_1('#skF_1'(A_50),A_50)
      | v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_95,c_18])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    ! [A_60,B_61] :
      ( k6_domain_1(A_60,B_61) = k1_tarski(B_61)
      | ~ m1_subset_1(B_61,A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_166,plain,(
    ! [A_68] :
      ( k6_domain_1(A_68,'#skF_1'(A_68)) = k1_tarski('#skF_1'(A_68))
      | v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_102,c_124])).

tff(c_40,plain,(
    ! [A_32,B_34] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_32),B_34),A_32)
      | ~ m1_subset_1(B_34,u1_struct_0(A_32))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_466,plain,(
    ! [A_119] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_119))),A_119)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_119)),u1_struct_0(A_119))
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119)
      | v1_xboole_0(u1_struct_0(A_119)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_40])).

tff(c_46,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

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

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k1_tarski(A_11),k1_zfmisc_1(B_12))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

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

tff(c_396,plain,(
    ! [C_102,B_103,A_104] :
      ( C_102 = B_103
      | ~ r1_tarski(B_103,C_102)
      | ~ v2_tex_2(C_102,A_104)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ v3_tex_2(B_103,A_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_398,plain,(
    ! [A_7,A_104] :
      ( A_7 = '#skF_4'
      | ~ v2_tex_2(A_7,A_104)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ v3_tex_2('#skF_4',A_104)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(resolution,[status(thm)],[c_60,c_396])).

tff(c_402,plain,(
    ! [A_105,A_106] :
      ( A_105 = '#skF_4'
      | ~ v2_tex_2(A_105,A_106)
      | ~ m1_subset_1(A_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ v3_tex_2('#skF_4',A_106)
      | ~ l1_pre_topc(A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_398])).

tff(c_421,plain,(
    ! [A_11,A_106] :
      ( k1_tarski(A_11) = '#skF_4'
      | ~ v2_tex_2(k1_tarski(A_11),A_106)
      | ~ v3_tex_2('#skF_4',A_106)
      | ~ l1_pre_topc(A_106)
      | ~ r2_hidden(A_11,u1_struct_0(A_106)) ) ),
    inference(resolution,[status(thm)],[c_16,c_402])).

tff(c_436,plain,(
    ! [A_11,A_106] :
      ( ~ v2_tex_2(k1_tarski(A_11),A_106)
      | ~ v3_tex_2('#skF_4',A_106)
      | ~ l1_pre_topc(A_106)
      | ~ r2_hidden(A_11,u1_struct_0(A_106)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_421])).

tff(c_519,plain,(
    ! [A_131] :
      ( ~ v3_tex_2('#skF_4',A_131)
      | ~ r2_hidden('#skF_1'(u1_struct_0(A_131)),u1_struct_0(A_131))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_131)),u1_struct_0(A_131))
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131)
      | v1_xboole_0(u1_struct_0(A_131)) ) ),
    inference(resolution,[status(thm)],[c_466,c_436])).

tff(c_533,plain,(
    ! [A_134] :
      ( ~ v3_tex_2('#skF_4',A_134)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_134)),u1_struct_0(A_134))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134)
      | v1_xboole_0(u1_struct_0(A_134)) ) ),
    inference(resolution,[status(thm)],[c_4,c_519])).

tff(c_538,plain,(
    ! [A_135] :
      ( ~ v3_tex_2('#skF_4',A_135)
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135)
      | v1_xboole_0(u1_struct_0(A_135)) ) ),
    inference(resolution,[status(thm)],[c_102,c_533])).

tff(c_24,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_547,plain,(
    ! [A_136] :
      ( ~ l1_struct_0(A_136)
      | ~ v3_tex_2('#skF_4',A_136)
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(resolution,[status(thm)],[c_538,c_24])).

tff(c_553,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_547])).

tff(c_557,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_553])).

tff(c_558,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_557])).

tff(c_561,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_558])).

tff(c_565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_561])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.39  
% 2.89/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.39  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.89/1.39  
% 2.89/1.39  %Foreground sorts:
% 2.89/1.39  
% 2.89/1.39  
% 2.89/1.39  %Background operators:
% 2.89/1.39  
% 2.89/1.39  
% 2.89/1.39  %Foreground operators:
% 2.89/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.89/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.89/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.89/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.89/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.89/1.39  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.89/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.39  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.89/1.39  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.89/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.89/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.89/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.89/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.89/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.89/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.39  
% 2.89/1.41  tff(f_123, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 2.89/1.41  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.89/1.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.89/1.41  tff(f_52, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.89/1.41  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.89/1.41  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 2.89/1.41  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.89/1.41  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.89/1.41  tff(f_42, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.89/1.41  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.89/1.41  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.89/1.41  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.89/1.41  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 2.89/1.41  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.89/1.41  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.89/1.41  tff(c_22, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.89/1.41  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.89/1.41  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.89/1.41  tff(c_42, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.89/1.41  tff(c_95, plain, (![A_50]: (v1_xboole_0(A_50) | r2_hidden('#skF_1'(A_50), A_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.89/1.41  tff(c_18, plain, (![A_13, B_14]: (m1_subset_1(A_13, B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.89/1.41  tff(c_102, plain, (![A_50]: (m1_subset_1('#skF_1'(A_50), A_50) | v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_95, c_18])).
% 2.89/1.41  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.89/1.41  tff(c_124, plain, (![A_60, B_61]: (k6_domain_1(A_60, B_61)=k1_tarski(B_61) | ~m1_subset_1(B_61, A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.89/1.41  tff(c_166, plain, (![A_68]: (k6_domain_1(A_68, '#skF_1'(A_68))=k1_tarski('#skF_1'(A_68)) | v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_102, c_124])).
% 2.89/1.41  tff(c_40, plain, (![A_32, B_34]: (v2_tex_2(k6_domain_1(u1_struct_0(A_32), B_34), A_32) | ~m1_subset_1(B_34, u1_struct_0(A_32)) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.89/1.41  tff(c_466, plain, (![A_119]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_119))), A_119) | ~m1_subset_1('#skF_1'(u1_struct_0(A_119)), u1_struct_0(A_119)) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119) | v1_xboole_0(u1_struct_0(A_119)))), inference(superposition, [status(thm), theory('equality')], [c_166, c_40])).
% 2.89/1.41  tff(c_46, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.89/1.41  tff(c_54, plain, (![A_37]: (k1_xboole_0=A_37 | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.89/1.41  tff(c_58, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_46, c_54])).
% 2.89/1.41  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.89/1.41  tff(c_66, plain, (![A_6]: (k2_xboole_0(A_6, '#skF_4')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_8])).
% 2.89/1.41  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.89/1.41  tff(c_88, plain, (![A_45, B_46]: (k2_xboole_0(k1_tarski(A_45), B_46)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_12])).
% 2.89/1.41  tff(c_92, plain, (![A_45]: (k1_tarski(A_45)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_66, c_88])).
% 2.89/1.41  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(k1_tarski(A_11), k1_zfmisc_1(B_12)) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.89/1.41  tff(c_14, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.89/1.41  tff(c_77, plain, (![A_10]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_14])).
% 2.89/1.41  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.89/1.41  tff(c_60, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_10])).
% 2.89/1.41  tff(c_396, plain, (![C_102, B_103, A_104]: (C_102=B_103 | ~r1_tarski(B_103, C_102) | ~v2_tex_2(C_102, A_104) | ~m1_subset_1(C_102, k1_zfmisc_1(u1_struct_0(A_104))) | ~v3_tex_2(B_103, A_104) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.89/1.41  tff(c_398, plain, (![A_7, A_104]: (A_7='#skF_4' | ~v2_tex_2(A_7, A_104) | ~m1_subset_1(A_7, k1_zfmisc_1(u1_struct_0(A_104))) | ~v3_tex_2('#skF_4', A_104) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(resolution, [status(thm)], [c_60, c_396])).
% 2.89/1.41  tff(c_402, plain, (![A_105, A_106]: (A_105='#skF_4' | ~v2_tex_2(A_105, A_106) | ~m1_subset_1(A_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~v3_tex_2('#skF_4', A_106) | ~l1_pre_topc(A_106))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_398])).
% 2.89/1.41  tff(c_421, plain, (![A_11, A_106]: (k1_tarski(A_11)='#skF_4' | ~v2_tex_2(k1_tarski(A_11), A_106) | ~v3_tex_2('#skF_4', A_106) | ~l1_pre_topc(A_106) | ~r2_hidden(A_11, u1_struct_0(A_106)))), inference(resolution, [status(thm)], [c_16, c_402])).
% 2.89/1.41  tff(c_436, plain, (![A_11, A_106]: (~v2_tex_2(k1_tarski(A_11), A_106) | ~v3_tex_2('#skF_4', A_106) | ~l1_pre_topc(A_106) | ~r2_hidden(A_11, u1_struct_0(A_106)))), inference(negUnitSimplification, [status(thm)], [c_92, c_421])).
% 2.89/1.41  tff(c_519, plain, (![A_131]: (~v3_tex_2('#skF_4', A_131) | ~r2_hidden('#skF_1'(u1_struct_0(A_131)), u1_struct_0(A_131)) | ~m1_subset_1('#skF_1'(u1_struct_0(A_131)), u1_struct_0(A_131)) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131) | v1_xboole_0(u1_struct_0(A_131)))), inference(resolution, [status(thm)], [c_466, c_436])).
% 2.89/1.41  tff(c_533, plain, (![A_134]: (~v3_tex_2('#skF_4', A_134) | ~m1_subset_1('#skF_1'(u1_struct_0(A_134)), u1_struct_0(A_134)) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134) | v1_xboole_0(u1_struct_0(A_134)))), inference(resolution, [status(thm)], [c_4, c_519])).
% 2.89/1.41  tff(c_538, plain, (![A_135]: (~v3_tex_2('#skF_4', A_135) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135) | v2_struct_0(A_135) | v1_xboole_0(u1_struct_0(A_135)))), inference(resolution, [status(thm)], [c_102, c_533])).
% 2.89/1.41  tff(c_24, plain, (![A_19]: (~v1_xboole_0(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.89/1.41  tff(c_547, plain, (![A_136]: (~l1_struct_0(A_136) | ~v3_tex_2('#skF_4', A_136) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(resolution, [status(thm)], [c_538, c_24])).
% 2.89/1.41  tff(c_553, plain, (~l1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_547])).
% 2.89/1.41  tff(c_557, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_553])).
% 2.89/1.41  tff(c_558, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_557])).
% 2.89/1.41  tff(c_561, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_22, c_558])).
% 2.89/1.41  tff(c_565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_561])).
% 2.89/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.41  
% 2.89/1.41  Inference rules
% 2.89/1.41  ----------------------
% 2.89/1.41  #Ref     : 0
% 2.89/1.41  #Sup     : 104
% 2.89/1.41  #Fact    : 0
% 2.89/1.41  #Define  : 0
% 2.89/1.41  #Split   : 0
% 2.89/1.41  #Chain   : 0
% 2.89/1.41  #Close   : 0
% 2.89/1.41  
% 2.89/1.41  Ordering : KBO
% 2.89/1.41  
% 2.89/1.41  Simplification rules
% 2.89/1.41  ----------------------
% 2.89/1.41  #Subsume      : 3
% 2.89/1.41  #Demod        : 13
% 2.89/1.41  #Tautology    : 26
% 2.89/1.41  #SimpNegUnit  : 2
% 2.89/1.41  #BackRed      : 2
% 2.89/1.41  
% 2.89/1.41  #Partial instantiations: 0
% 2.89/1.41  #Strategies tried      : 1
% 2.89/1.41  
% 2.89/1.41  Timing (in seconds)
% 2.89/1.41  ----------------------
% 2.89/1.41  Preprocessing        : 0.32
% 2.89/1.41  Parsing              : 0.17
% 2.89/1.41  CNF conversion       : 0.02
% 2.89/1.41  Main loop            : 0.33
% 2.89/1.41  Inferencing          : 0.13
% 2.89/1.41  Reduction            : 0.08
% 2.89/1.41  Demodulation         : 0.06
% 2.89/1.41  BG Simplification    : 0.02
% 2.89/1.41  Subsumption          : 0.07
% 2.89/1.41  Abstraction          : 0.02
% 2.89/1.41  MUC search           : 0.00
% 2.89/1.41  Cooper               : 0.00
% 2.89/1.41  Total                : 0.68
% 2.89/1.41  Index Insertion      : 0.00
% 2.89/1.41  Index Deletion       : 0.00
% 2.89/1.41  Index Matching       : 0.00
% 2.89/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
