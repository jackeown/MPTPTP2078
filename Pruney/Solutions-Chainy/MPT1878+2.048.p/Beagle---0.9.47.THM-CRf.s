%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:03 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 155 expanded)
%              Number of leaves         :   42 (  70 expanded)
%              Depth                    :   18
%              Number of atoms          :  173 ( 346 expanded)
%              Number of equality atoms :   44 (  76 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_145,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_117,axiom,(
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

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_26,plain,(
    ! [A_39] :
      ( l1_struct_0(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_50,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_54,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_46,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_58,plain,(
    ! [A_58] :
      ( k1_xboole_0 = A_58
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_58])).

tff(c_24,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_1'(A_17),A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_102,plain,(
    ! [A_69] :
      ( r2_hidden('#skF_1'(A_69),A_69)
      | A_69 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_24])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_106,plain,(
    ! [A_69] :
      ( m1_subset_1('#skF_1'(A_69),A_69)
      | A_69 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_102,c_18])).

tff(c_136,plain,(
    ! [A_76,B_77] :
      ( k6_domain_1(A_76,B_77) = k1_tarski(B_77)
      | ~ m1_subset_1(B_77,A_76)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_143,plain,(
    ! [A_69] :
      ( k6_domain_1(A_69,'#skF_1'(A_69)) = k1_tarski('#skF_1'(A_69))
      | v1_xboole_0(A_69)
      | A_69 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_106,c_136])).

tff(c_227,plain,(
    ! [A_96,B_97] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_96),B_97),A_96)
      | ~ m1_subset_1(B_97,u1_struct_0(A_96))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_576,plain,(
    ! [A_170] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_170))),A_170)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_170)),u1_struct_0(A_170))
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170)
      | v1_xboole_0(u1_struct_0(A_170))
      | u1_struct_0(A_170) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_227])).

tff(c_8,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [A_4] : k5_xboole_0(A_4,'#skF_4') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_8])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_84,plain,(
    ! [A_3] : k4_xboole_0('#skF_4',A_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_6])).

tff(c_109,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k4_xboole_0(B_73,A_72)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_118,plain,(
    ! [A_3] : k5_xboole_0(A_3,'#skF_4') = k2_xboole_0(A_3,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_109])).

tff(c_122,plain,(
    ! [A_74] : k2_xboole_0(A_74,'#skF_4') = A_74 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_118])).

tff(c_12,plain,(
    ! [A_7,B_8] : k2_xboole_0(k1_tarski(A_7),B_8) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_98,plain,(
    ! [A_7,B_8] : k2_xboole_0(k1_tarski(A_7),B_8) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_12])).

tff(c_129,plain,(
    ! [A_7] : k1_tarski(A_7) != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_98])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( m1_subset_1(k1_tarski(B_11),k1_zfmisc_1(A_10))
      | k1_xboole_0 = A_10
      | ~ m1_subset_1(B_11,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_173,plain,(
    ! [B_11,A_10] :
      ( m1_subset_1(k1_tarski(B_11),k1_zfmisc_1(A_10))
      | A_10 = '#skF_4'
      | ~ m1_subset_1(B_11,A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_16])).

tff(c_14,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_71,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_14])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [A_2] : r1_tarski('#skF_4',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4])).

tff(c_458,plain,(
    ! [C_137,B_138,A_139] :
      ( C_137 = B_138
      | ~ r1_tarski(B_138,C_137)
      | ~ v2_tex_2(C_137,A_139)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ v3_tex_2(B_138,A_139)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_pre_topc(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_460,plain,(
    ! [A_2,A_139] :
      ( A_2 = '#skF_4'
      | ~ v2_tex_2(A_2,A_139)
      | ~ m1_subset_1(A_2,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ v3_tex_2('#skF_4',A_139)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_pre_topc(A_139) ) ),
    inference(resolution,[status(thm)],[c_64,c_458])).

tff(c_464,plain,(
    ! [A_140,A_141] :
      ( A_140 = '#skF_4'
      | ~ v2_tex_2(A_140,A_141)
      | ~ m1_subset_1(A_140,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ v3_tex_2('#skF_4',A_141)
      | ~ l1_pre_topc(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_460])).

tff(c_483,plain,(
    ! [B_11,A_141] :
      ( k1_tarski(B_11) = '#skF_4'
      | ~ v2_tex_2(k1_tarski(B_11),A_141)
      | ~ v3_tex_2('#skF_4',A_141)
      | ~ l1_pre_topc(A_141)
      | u1_struct_0(A_141) = '#skF_4'
      | ~ m1_subset_1(B_11,u1_struct_0(A_141)) ) ),
    inference(resolution,[status(thm)],[c_173,c_464])).

tff(c_498,plain,(
    ! [B_11,A_141] :
      ( ~ v2_tex_2(k1_tarski(B_11),A_141)
      | ~ v3_tex_2('#skF_4',A_141)
      | ~ l1_pre_topc(A_141)
      | u1_struct_0(A_141) = '#skF_4'
      | ~ m1_subset_1(B_11,u1_struct_0(A_141)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_483])).

tff(c_581,plain,(
    ! [A_171] :
      ( ~ v3_tex_2('#skF_4',A_171)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_171)),u1_struct_0(A_171))
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171)
      | v1_xboole_0(u1_struct_0(A_171))
      | u1_struct_0(A_171) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_576,c_498])).

tff(c_586,plain,(
    ! [A_172] :
      ( ~ v3_tex_2('#skF_4',A_172)
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172)
      | v1_xboole_0(u1_struct_0(A_172))
      | u1_struct_0(A_172) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_106,c_581])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2])).

tff(c_595,plain,(
    ! [A_173] :
      ( ~ v3_tex_2('#skF_4',A_173)
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173)
      | u1_struct_0(A_173) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_586,c_63])).

tff(c_601,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_595])).

tff(c_605,plain,
    ( v2_struct_0('#skF_3')
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_601])).

tff(c_606,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_605])).

tff(c_28,plain,(
    ! [A_40] :
      ( ~ v1_xboole_0(u1_struct_0(A_40))
      | ~ l1_struct_0(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_644,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_28])).

tff(c_674,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_644])).

tff(c_675,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_674])).

tff(c_679,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_675])).

tff(c_683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_679])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.42  
% 2.84/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.42  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.84/1.42  
% 2.84/1.42  %Foreground sorts:
% 2.84/1.42  
% 2.84/1.42  
% 2.84/1.42  %Background operators:
% 2.84/1.42  
% 2.84/1.42  
% 2.84/1.42  %Foreground operators:
% 2.84/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.84/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.84/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.84/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.84/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.84/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.84/1.42  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.84/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.42  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.84/1.42  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.84/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.84/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.84/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.84/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.84/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.84/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.84/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.84/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.84/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.84/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.42  
% 3.09/1.44  tff(f_145, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 3.09/1.44  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.09/1.44  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.09/1.44  tff(f_80, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 3.09/1.44  tff(f_53, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.09/1.44  tff(f_99, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.09/1.44  tff(f_129, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 3.09/1.44  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.09/1.44  tff(f_33, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.09/1.44  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.09/1.44  tff(f_40, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.09/1.44  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 3.09/1.44  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.09/1.44  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.09/1.44  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.09/1.44  tff(f_92, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.09/1.44  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.09/1.44  tff(c_26, plain, (![A_39]: (l1_struct_0(A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.09/1.44  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.09/1.44  tff(c_50, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.09/1.44  tff(c_54, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.09/1.44  tff(c_46, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.09/1.44  tff(c_58, plain, (![A_58]: (k1_xboole_0=A_58 | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.09/1.44  tff(c_62, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_58])).
% 3.09/1.44  tff(c_24, plain, (![A_17]: (r2_hidden('#skF_1'(A_17), A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.09/1.44  tff(c_102, plain, (![A_69]: (r2_hidden('#skF_1'(A_69), A_69) | A_69='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_24])).
% 3.09/1.44  tff(c_18, plain, (![A_12, B_13]: (m1_subset_1(A_12, B_13) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.09/1.44  tff(c_106, plain, (![A_69]: (m1_subset_1('#skF_1'(A_69), A_69) | A_69='#skF_4')), inference(resolution, [status(thm)], [c_102, c_18])).
% 3.09/1.44  tff(c_136, plain, (![A_76, B_77]: (k6_domain_1(A_76, B_77)=k1_tarski(B_77) | ~m1_subset_1(B_77, A_76) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.09/1.44  tff(c_143, plain, (![A_69]: (k6_domain_1(A_69, '#skF_1'(A_69))=k1_tarski('#skF_1'(A_69)) | v1_xboole_0(A_69) | A_69='#skF_4')), inference(resolution, [status(thm)], [c_106, c_136])).
% 3.09/1.44  tff(c_227, plain, (![A_96, B_97]: (v2_tex_2(k6_domain_1(u1_struct_0(A_96), B_97), A_96) | ~m1_subset_1(B_97, u1_struct_0(A_96)) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.09/1.44  tff(c_576, plain, (![A_170]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_170))), A_170) | ~m1_subset_1('#skF_1'(u1_struct_0(A_170)), u1_struct_0(A_170)) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170) | v1_xboole_0(u1_struct_0(A_170)) | u1_struct_0(A_170)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_143, c_227])).
% 3.09/1.44  tff(c_8, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.09/1.44  tff(c_74, plain, (![A_4]: (k5_xboole_0(A_4, '#skF_4')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_8])).
% 3.09/1.44  tff(c_6, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.09/1.44  tff(c_84, plain, (![A_3]: (k4_xboole_0('#skF_4', A_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_6])).
% 3.09/1.44  tff(c_109, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k4_xboole_0(B_73, A_72))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.09/1.44  tff(c_118, plain, (![A_3]: (k5_xboole_0(A_3, '#skF_4')=k2_xboole_0(A_3, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_109])).
% 3.09/1.44  tff(c_122, plain, (![A_74]: (k2_xboole_0(A_74, '#skF_4')=A_74)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_118])).
% 3.09/1.44  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(k1_tarski(A_7), B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.09/1.44  tff(c_98, plain, (![A_7, B_8]: (k2_xboole_0(k1_tarski(A_7), B_8)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_12])).
% 3.09/1.44  tff(c_129, plain, (![A_7]: (k1_tarski(A_7)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_122, c_98])).
% 3.09/1.44  tff(c_16, plain, (![B_11, A_10]: (m1_subset_1(k1_tarski(B_11), k1_zfmisc_1(A_10)) | k1_xboole_0=A_10 | ~m1_subset_1(B_11, A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.09/1.44  tff(c_173, plain, (![B_11, A_10]: (m1_subset_1(k1_tarski(B_11), k1_zfmisc_1(A_10)) | A_10='#skF_4' | ~m1_subset_1(B_11, A_10))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_16])).
% 3.09/1.44  tff(c_14, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.09/1.44  tff(c_71, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_14])).
% 3.09/1.44  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.09/1.44  tff(c_64, plain, (![A_2]: (r1_tarski('#skF_4', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4])).
% 3.09/1.44  tff(c_458, plain, (![C_137, B_138, A_139]: (C_137=B_138 | ~r1_tarski(B_138, C_137) | ~v2_tex_2(C_137, A_139) | ~m1_subset_1(C_137, k1_zfmisc_1(u1_struct_0(A_139))) | ~v3_tex_2(B_138, A_139) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_pre_topc(A_139))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.09/1.44  tff(c_460, plain, (![A_2, A_139]: (A_2='#skF_4' | ~v2_tex_2(A_2, A_139) | ~m1_subset_1(A_2, k1_zfmisc_1(u1_struct_0(A_139))) | ~v3_tex_2('#skF_4', A_139) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_pre_topc(A_139))), inference(resolution, [status(thm)], [c_64, c_458])).
% 3.09/1.44  tff(c_464, plain, (![A_140, A_141]: (A_140='#skF_4' | ~v2_tex_2(A_140, A_141) | ~m1_subset_1(A_140, k1_zfmisc_1(u1_struct_0(A_141))) | ~v3_tex_2('#skF_4', A_141) | ~l1_pre_topc(A_141))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_460])).
% 3.09/1.44  tff(c_483, plain, (![B_11, A_141]: (k1_tarski(B_11)='#skF_4' | ~v2_tex_2(k1_tarski(B_11), A_141) | ~v3_tex_2('#skF_4', A_141) | ~l1_pre_topc(A_141) | u1_struct_0(A_141)='#skF_4' | ~m1_subset_1(B_11, u1_struct_0(A_141)))), inference(resolution, [status(thm)], [c_173, c_464])).
% 3.09/1.44  tff(c_498, plain, (![B_11, A_141]: (~v2_tex_2(k1_tarski(B_11), A_141) | ~v3_tex_2('#skF_4', A_141) | ~l1_pre_topc(A_141) | u1_struct_0(A_141)='#skF_4' | ~m1_subset_1(B_11, u1_struct_0(A_141)))), inference(negUnitSimplification, [status(thm)], [c_129, c_483])).
% 3.09/1.44  tff(c_581, plain, (![A_171]: (~v3_tex_2('#skF_4', A_171) | ~m1_subset_1('#skF_1'(u1_struct_0(A_171)), u1_struct_0(A_171)) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171) | v1_xboole_0(u1_struct_0(A_171)) | u1_struct_0(A_171)='#skF_4')), inference(resolution, [status(thm)], [c_576, c_498])).
% 3.09/1.44  tff(c_586, plain, (![A_172]: (~v3_tex_2('#skF_4', A_172) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172) | v1_xboole_0(u1_struct_0(A_172)) | u1_struct_0(A_172)='#skF_4')), inference(resolution, [status(thm)], [c_106, c_581])).
% 3.09/1.44  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.09/1.44  tff(c_63, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2])).
% 3.09/1.44  tff(c_595, plain, (![A_173]: (~v3_tex_2('#skF_4', A_173) | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173) | u1_struct_0(A_173)='#skF_4')), inference(resolution, [status(thm)], [c_586, c_63])).
% 3.09/1.44  tff(c_601, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_46, c_595])).
% 3.09/1.44  tff(c_605, plain, (v2_struct_0('#skF_3') | u1_struct_0('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_601])).
% 3.09/1.44  tff(c_606, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_56, c_605])).
% 3.09/1.44  tff(c_28, plain, (![A_40]: (~v1_xboole_0(u1_struct_0(A_40)) | ~l1_struct_0(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.09/1.44  tff(c_644, plain, (~v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_606, c_28])).
% 3.09/1.44  tff(c_674, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_644])).
% 3.09/1.44  tff(c_675, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_674])).
% 3.09/1.44  tff(c_679, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_675])).
% 3.09/1.44  tff(c_683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_679])).
% 3.09/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.44  
% 3.09/1.44  Inference rules
% 3.09/1.44  ----------------------
% 3.09/1.44  #Ref     : 0
% 3.09/1.44  #Sup     : 127
% 3.09/1.44  #Fact    : 0
% 3.09/1.44  #Define  : 0
% 3.09/1.44  #Split   : 0
% 3.09/1.44  #Chain   : 0
% 3.09/1.44  #Close   : 0
% 3.09/1.44  
% 3.09/1.44  Ordering : KBO
% 3.09/1.44  
% 3.09/1.44  Simplification rules
% 3.09/1.44  ----------------------
% 3.09/1.44  #Subsume      : 3
% 3.09/1.44  #Demod        : 49
% 3.09/1.44  #Tautology    : 34
% 3.09/1.44  #SimpNegUnit  : 8
% 3.09/1.44  #BackRed      : 2
% 3.09/1.44  
% 3.09/1.44  #Partial instantiations: 0
% 3.09/1.44  #Strategies tried      : 1
% 3.09/1.44  
% 3.09/1.44  Timing (in seconds)
% 3.09/1.44  ----------------------
% 3.09/1.44  Preprocessing        : 0.32
% 3.09/1.44  Parsing              : 0.17
% 3.09/1.44  CNF conversion       : 0.02
% 3.09/1.44  Main loop            : 0.36
% 3.09/1.44  Inferencing          : 0.14
% 3.09/1.44  Reduction            : 0.10
% 3.09/1.44  Demodulation         : 0.06
% 3.09/1.44  BG Simplification    : 0.02
% 3.09/1.44  Subsumption          : 0.07
% 3.09/1.44  Abstraction          : 0.02
% 3.09/1.44  MUC search           : 0.00
% 3.09/1.44  Cooper               : 0.00
% 3.09/1.44  Total                : 0.71
% 3.09/1.44  Index Insertion      : 0.00
% 3.09/1.44  Index Deletion       : 0.00
% 3.09/1.44  Index Matching       : 0.00
% 3.09/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
