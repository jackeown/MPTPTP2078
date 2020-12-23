%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:27 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.34s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 202 expanded)
%              Number of leaves         :   32 (  85 expanded)
%              Depth                    :   13
%              Number of atoms          :  121 ( 462 expanded)
%              Number of equality atoms :   27 (  87 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_38,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_34,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_38,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_46,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_46])).

tff(c_16,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_57,plain,(
    ! [A_12] : m1_subset_1('#skF_4',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_16])).

tff(c_295,plain,(
    ! [A_77,B_78] :
      ( r1_tarski('#skF_2'(A_77,B_78),B_78)
      | v2_tex_2(B_78,A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_400,plain,(
    ! [A_85] :
      ( r1_tarski('#skF_2'(A_85,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_57,c_295])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_73,plain,(
    ! [A_6] :
      ( A_6 = '#skF_4'
      | ~ r1_tarski(A_6,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_55,c_10])).

tff(c_405,plain,(
    ! [A_86] :
      ( '#skF_2'(A_86,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_400,c_73])).

tff(c_408,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_405,c_34])).

tff(c_411,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_408])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_385,plain,(
    ! [A_83,B_84] :
      ( m1_subset_1('#skF_2'(A_83,B_84),k1_zfmisc_1(u1_struct_0(A_83)))
      | v2_tex_2(B_84,A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    ! [B_18,A_16] :
      ( v4_pre_topc(B_18,A_16)
      | ~ v1_xboole_0(B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1541,plain,(
    ! [A_128,B_129] :
      ( v4_pre_topc('#skF_2'(A_128,B_129),A_128)
      | ~ v1_xboole_0('#skF_2'(A_128,B_129))
      | ~ v2_pre_topc(A_128)
      | v2_tex_2(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_385,c_20])).

tff(c_1760,plain,(
    ! [A_134] :
      ( v4_pre_topc('#skF_2'(A_134,'#skF_4'),A_134)
      | ~ v1_xboole_0('#skF_2'(A_134,'#skF_4'))
      | ~ v2_pre_topc(A_134)
      | v2_tex_2('#skF_4',A_134)
      | ~ l1_pre_topc(A_134) ) ),
    inference(resolution,[status(thm)],[c_57,c_1541])).

tff(c_1763,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_pre_topc('#skF_3')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_1760])).

tff(c_1765,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_38,c_411,c_1763])).

tff(c_1766,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1765])).

tff(c_128,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k4_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_74,plain,(
    ! [A_51] :
      ( A_51 = '#skF_4'
      | ~ r1_tarski(A_51,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_55,c_10])).

tff(c_79,plain,(
    ! [B_5] : k4_xboole_0('#skF_4',B_5) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_74])).

tff(c_158,plain,(
    ! [B_57] : k3_xboole_0('#skF_4',B_57) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_79])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_166,plain,(
    ! [B_57] : k3_xboole_0(B_57,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_2])).

tff(c_220,plain,(
    ! [A_62,B_63,C_64] :
      ( k9_subset_1(A_62,B_63,C_64) = k3_xboole_0(B_63,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_222,plain,(
    ! [A_12,B_63] : k9_subset_1(A_12,B_63,'#skF_4') = k3_xboole_0(B_63,'#skF_4') ),
    inference(resolution,[status(thm)],[c_57,c_220])).

tff(c_224,plain,(
    ! [A_12,B_63] : k9_subset_1(A_12,B_63,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_222])).

tff(c_884,plain,(
    ! [A_105,B_106,D_107] :
      ( k9_subset_1(u1_struct_0(A_105),B_106,D_107) != '#skF_2'(A_105,B_106)
      | ~ v4_pre_topc(D_107,A_105)
      | ~ m1_subset_1(D_107,k1_zfmisc_1(u1_struct_0(A_105)))
      | v2_tex_2(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_887,plain,(
    ! [A_105,B_63] :
      ( '#skF_2'(A_105,B_63) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_105)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_105)))
      | v2_tex_2(B_63,A_105)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_884])).

tff(c_2576,plain,(
    ! [A_153,B_154] :
      ( '#skF_2'(A_153,B_154) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_153)
      | v2_tex_2(B_154,A_153)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_887])).

tff(c_2590,plain,(
    ! [A_155] :
      ( '#skF_2'(A_155,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_155)
      | v2_tex_2('#skF_4',A_155)
      | ~ l1_pre_topc(A_155) ) ),
    inference(resolution,[status(thm)],[c_57,c_2576])).

tff(c_2593,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1766,c_2590])).

tff(c_2599,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_411,c_2593])).

tff(c_2601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_2599])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:32:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.10/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/1.78  
% 4.10/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/1.78  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 4.10/1.78  
% 4.10/1.78  %Foreground sorts:
% 4.10/1.78  
% 4.10/1.78  
% 4.10/1.78  %Background operators:
% 4.10/1.78  
% 4.10/1.78  
% 4.10/1.78  %Foreground operators:
% 4.10/1.78  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.10/1.78  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.10/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.10/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.10/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.10/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.10/1.78  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.10/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.10/1.78  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.10/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.10/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.10/1.78  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.10/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.10/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.10/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.10/1.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.10/1.78  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.10/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.10/1.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.10/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.10/1.78  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.10/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.10/1.78  
% 4.34/1.79  tff(f_99, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 4.34/1.79  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.34/1.79  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.34/1.79  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 4.34/1.79  tff(f_38, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.34/1.79  tff(f_63, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 4.34/1.79  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.34/1.79  tff(f_34, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.34/1.79  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.34/1.79  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.34/1.79  tff(c_34, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.34/1.79  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.34/1.79  tff(c_38, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.34/1.79  tff(c_46, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.34/1.79  tff(c_55, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_38, c_46])).
% 4.34/1.79  tff(c_16, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.34/1.79  tff(c_57, plain, (![A_12]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_16])).
% 4.34/1.79  tff(c_295, plain, (![A_77, B_78]: (r1_tarski('#skF_2'(A_77, B_78), B_78) | v2_tex_2(B_78, A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.34/1.79  tff(c_400, plain, (![A_85]: (r1_tarski('#skF_2'(A_85, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_85) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_57, c_295])).
% 4.34/1.79  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.34/1.79  tff(c_73, plain, (![A_6]: (A_6='#skF_4' | ~r1_tarski(A_6, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_55, c_10])).
% 4.34/1.79  tff(c_405, plain, (![A_86]: ('#skF_2'(A_86, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_86) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_400, c_73])).
% 4.34/1.79  tff(c_408, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_405, c_34])).
% 4.34/1.79  tff(c_411, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_408])).
% 4.34/1.79  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.34/1.79  tff(c_385, plain, (![A_83, B_84]: (m1_subset_1('#skF_2'(A_83, B_84), k1_zfmisc_1(u1_struct_0(A_83))) | v2_tex_2(B_84, A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.34/1.79  tff(c_20, plain, (![B_18, A_16]: (v4_pre_topc(B_18, A_16) | ~v1_xboole_0(B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.34/1.79  tff(c_1541, plain, (![A_128, B_129]: (v4_pre_topc('#skF_2'(A_128, B_129), A_128) | ~v1_xboole_0('#skF_2'(A_128, B_129)) | ~v2_pre_topc(A_128) | v2_tex_2(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(resolution, [status(thm)], [c_385, c_20])).
% 4.34/1.79  tff(c_1760, plain, (![A_134]: (v4_pre_topc('#skF_2'(A_134, '#skF_4'), A_134) | ~v1_xboole_0('#skF_2'(A_134, '#skF_4')) | ~v2_pre_topc(A_134) | v2_tex_2('#skF_4', A_134) | ~l1_pre_topc(A_134))), inference(resolution, [status(thm)], [c_57, c_1541])).
% 4.34/1.79  tff(c_1763, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_pre_topc('#skF_3') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_411, c_1760])).
% 4.34/1.79  tff(c_1765, plain, (v4_pre_topc('#skF_4', '#skF_3') | v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_38, c_411, c_1763])).
% 4.34/1.79  tff(c_1766, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_1765])).
% 4.34/1.79  tff(c_128, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k4_xboole_0(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.34/1.79  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.34/1.79  tff(c_74, plain, (![A_51]: (A_51='#skF_4' | ~r1_tarski(A_51, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_55, c_10])).
% 4.34/1.79  tff(c_79, plain, (![B_5]: (k4_xboole_0('#skF_4', B_5)='#skF_4')), inference(resolution, [status(thm)], [c_8, c_74])).
% 4.34/1.79  tff(c_158, plain, (![B_57]: (k3_xboole_0('#skF_4', B_57)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_128, c_79])).
% 4.34/1.79  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.34/1.79  tff(c_166, plain, (![B_57]: (k3_xboole_0(B_57, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_158, c_2])).
% 4.34/1.79  tff(c_220, plain, (![A_62, B_63, C_64]: (k9_subset_1(A_62, B_63, C_64)=k3_xboole_0(B_63, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.34/1.79  tff(c_222, plain, (![A_12, B_63]: (k9_subset_1(A_12, B_63, '#skF_4')=k3_xboole_0(B_63, '#skF_4'))), inference(resolution, [status(thm)], [c_57, c_220])).
% 4.34/1.79  tff(c_224, plain, (![A_12, B_63]: (k9_subset_1(A_12, B_63, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_222])).
% 4.34/1.79  tff(c_884, plain, (![A_105, B_106, D_107]: (k9_subset_1(u1_struct_0(A_105), B_106, D_107)!='#skF_2'(A_105, B_106) | ~v4_pre_topc(D_107, A_105) | ~m1_subset_1(D_107, k1_zfmisc_1(u1_struct_0(A_105))) | v2_tex_2(B_106, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.34/1.79  tff(c_887, plain, (![A_105, B_63]: ('#skF_2'(A_105, B_63)!='#skF_4' | ~v4_pre_topc('#skF_4', A_105) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_105))) | v2_tex_2(B_63, A_105) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(superposition, [status(thm), theory('equality')], [c_224, c_884])).
% 4.34/1.79  tff(c_2576, plain, (![A_153, B_154]: ('#skF_2'(A_153, B_154)!='#skF_4' | ~v4_pre_topc('#skF_4', A_153) | v2_tex_2(B_154, A_153) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_887])).
% 4.34/1.79  tff(c_2590, plain, (![A_155]: ('#skF_2'(A_155, '#skF_4')!='#skF_4' | ~v4_pre_topc('#skF_4', A_155) | v2_tex_2('#skF_4', A_155) | ~l1_pre_topc(A_155))), inference(resolution, [status(thm)], [c_57, c_2576])).
% 4.34/1.79  tff(c_2593, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1766, c_2590])).
% 4.34/1.79  tff(c_2599, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_411, c_2593])).
% 4.34/1.79  tff(c_2601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_2599])).
% 4.34/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.34/1.79  
% 4.34/1.79  Inference rules
% 4.34/1.79  ----------------------
% 4.34/1.79  #Ref     : 0
% 4.34/1.79  #Sup     : 614
% 4.34/1.79  #Fact    : 0
% 4.34/1.79  #Define  : 0
% 4.34/1.79  #Split   : 0
% 4.34/1.79  #Chain   : 0
% 4.34/1.79  #Close   : 0
% 4.34/1.79  
% 4.34/1.79  Ordering : KBO
% 4.34/1.79  
% 4.34/1.79  Simplification rules
% 4.34/1.79  ----------------------
% 4.34/1.79  #Subsume      : 10
% 4.34/1.79  #Demod        : 979
% 4.34/1.79  #Tautology    : 407
% 4.34/1.79  #SimpNegUnit  : 8
% 4.34/1.79  #BackRed      : 3
% 4.34/1.79  
% 4.34/1.79  #Partial instantiations: 0
% 4.34/1.79  #Strategies tried      : 1
% 4.34/1.79  
% 4.34/1.79  Timing (in seconds)
% 4.34/1.79  ----------------------
% 4.34/1.80  Preprocessing        : 0.31
% 4.34/1.80  Parsing              : 0.16
% 4.34/1.80  CNF conversion       : 0.02
% 4.34/1.80  Main loop            : 0.72
% 4.34/1.80  Inferencing          : 0.20
% 4.34/1.80  Reduction            : 0.38
% 4.34/1.80  Demodulation         : 0.34
% 4.34/1.80  BG Simplification    : 0.03
% 4.34/1.80  Subsumption          : 0.08
% 4.34/1.80  Abstraction          : 0.03
% 4.34/1.80  MUC search           : 0.00
% 4.34/1.80  Cooper               : 0.00
% 4.34/1.80  Total                : 1.06
% 4.34/1.80  Index Insertion      : 0.00
% 4.34/1.80  Index Deletion       : 0.00
% 4.34/1.80  Index Matching       : 0.00
% 4.34/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
