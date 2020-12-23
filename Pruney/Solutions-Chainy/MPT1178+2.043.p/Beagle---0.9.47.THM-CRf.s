%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:08 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 121 expanded)
%              Number of leaves         :   46 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  120 ( 329 expanded)
%              Number of equality atoms :   17 (  41 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_orders_2 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_orders_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_151,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( C = k4_orders_2(A,B)
            <=> ! [D] :
                  ( r2_hidden(D,C)
                <=> m2_orders_2(D,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_133,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_30,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_66,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_64,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_62,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_60,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_58,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_307,plain,(
    ! [A_121,B_122] :
      ( m2_orders_2('#skF_3'(A_121,B_122),A_121,B_122)
      | ~ m1_orders_1(B_122,k1_orders_1(u1_struct_0(A_121)))
      | ~ l1_orders_2(A_121)
      | ~ v5_orders_2(A_121)
      | ~ v4_orders_2(A_121)
      | ~ v3_orders_2(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_309,plain,
    ( m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_307])).

tff(c_312,plain,
    ( m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_309])).

tff(c_313,plain,(
    m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_312])).

tff(c_56,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_314,plain,(
    ! [D_123,A_124,B_125] :
      ( r2_hidden(D_123,k4_orders_2(A_124,B_125))
      | ~ m2_orders_2(D_123,A_124,B_125)
      | ~ m1_orders_1(B_125,k1_orders_1(u1_struct_0(A_124)))
      | ~ l1_orders_2(A_124)
      | ~ v5_orders_2(A_124)
      | ~ v4_orders_2(A_124)
      | ~ v3_orders_2(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_316,plain,(
    ! [D_123] :
      ( r2_hidden(D_123,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_123,'#skF_5','#skF_6')
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_314])).

tff(c_319,plain,(
    ! [D_123] :
      ( r2_hidden(D_123,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_123,'#skF_5','#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_316])).

tff(c_326,plain,(
    ! [D_129] :
      ( r2_hidden(D_129,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_129,'#skF_5','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_319])).

tff(c_50,plain,(
    ! [A_70,B_73] :
      ( k3_tarski(A_70) != k1_xboole_0
      | ~ r2_hidden(B_73,A_70)
      | k1_xboole_0 = B_73 ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_331,plain,(
    ! [D_129] :
      ( k3_tarski(k4_orders_2('#skF_5','#skF_6')) != k1_xboole_0
      | k1_xboole_0 = D_129
      | ~ m2_orders_2(D_129,'#skF_5','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_326,c_50])).

tff(c_339,plain,(
    ! [D_130] :
      ( k1_xboole_0 = D_130
      | ~ m2_orders_2(D_130,'#skF_5','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_331])).

tff(c_343,plain,(
    '#skF_3'('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_313,c_339])).

tff(c_344,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_313])).

tff(c_354,plain,(
    ! [B_131,A_132,C_133] :
      ( r2_hidden(k1_funct_1(B_131,u1_struct_0(A_132)),C_133)
      | ~ m2_orders_2(C_133,A_132,B_131)
      | ~ m1_orders_1(B_131,k1_orders_1(u1_struct_0(A_132)))
      | ~ l1_orders_2(A_132)
      | ~ v5_orders_2(A_132)
      | ~ v4_orders_2(A_132)
      | ~ v3_orders_2(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_199,plain,(
    ! [B_91,A_92] :
      ( ~ r2_hidden(B_91,A_92)
      | k4_xboole_0(A_92,k1_tarski(B_91)) != A_92 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_208,plain,(
    ! [B_91] : ~ r2_hidden(B_91,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_199])).

tff(c_368,plain,(
    ! [A_134,B_135] :
      ( ~ m2_orders_2(k1_xboole_0,A_134,B_135)
      | ~ m1_orders_1(B_135,k1_orders_1(u1_struct_0(A_134)))
      | ~ l1_orders_2(A_134)
      | ~ v5_orders_2(A_134)
      | ~ v4_orders_2(A_134)
      | ~ v3_orders_2(A_134)
      | v2_struct_0(A_134) ) ),
    inference(resolution,[status(thm)],[c_354,c_208])).

tff(c_371,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_368])).

tff(c_374,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_344,c_371])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_374])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:53:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.31  
% 2.36/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.31  %$ m2_orders_2 > r2_hidden > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_orders_2 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_orders_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 2.36/1.31  
% 2.36/1.31  %Foreground sorts:
% 2.36/1.31  
% 2.36/1.31  
% 2.36/1.31  %Background operators:
% 2.36/1.31  
% 2.36/1.31  
% 2.36/1.31  %Foreground operators:
% 2.36/1.31  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.36/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.36/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.36/1.31  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.36/1.31  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.36/1.31  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.36/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.36/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.36/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.31  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.36/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.36/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.36/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.36/1.31  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.36/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.36/1.31  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.36/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.36/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.36/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.36/1.31  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.36/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.36/1.31  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.36/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.31  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.36/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.36/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.31  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.36/1.31  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.36/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.36/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.36/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.36/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.36/1.31  
% 2.66/1.32  tff(f_151, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.66/1.32  tff(f_94, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 2.66/1.32  tff(f_76, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.66/1.32  tff(f_133, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 2.66/1.32  tff(f_113, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 2.66/1.32  tff(f_30, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.66/1.32  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.66/1.32  tff(c_68, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.66/1.32  tff(c_66, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.66/1.32  tff(c_64, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.66/1.32  tff(c_62, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.66/1.32  tff(c_60, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.66/1.32  tff(c_58, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.66/1.32  tff(c_307, plain, (![A_121, B_122]: (m2_orders_2('#skF_3'(A_121, B_122), A_121, B_122) | ~m1_orders_1(B_122, k1_orders_1(u1_struct_0(A_121))) | ~l1_orders_2(A_121) | ~v5_orders_2(A_121) | ~v4_orders_2(A_121) | ~v3_orders_2(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.66/1.32  tff(c_309, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_58, c_307])).
% 2.66/1.32  tff(c_312, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_309])).
% 2.66/1.32  tff(c_313, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_312])).
% 2.66/1.32  tff(c_56, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.66/1.32  tff(c_314, plain, (![D_123, A_124, B_125]: (r2_hidden(D_123, k4_orders_2(A_124, B_125)) | ~m2_orders_2(D_123, A_124, B_125) | ~m1_orders_1(B_125, k1_orders_1(u1_struct_0(A_124))) | ~l1_orders_2(A_124) | ~v5_orders_2(A_124) | ~v4_orders_2(A_124) | ~v3_orders_2(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.66/1.32  tff(c_316, plain, (![D_123]: (r2_hidden(D_123, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_123, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_314])).
% 2.66/1.32  tff(c_319, plain, (![D_123]: (r2_hidden(D_123, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_123, '#skF_5', '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_316])).
% 2.66/1.32  tff(c_326, plain, (![D_129]: (r2_hidden(D_129, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_129, '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_68, c_319])).
% 2.66/1.32  tff(c_50, plain, (![A_70, B_73]: (k3_tarski(A_70)!=k1_xboole_0 | ~r2_hidden(B_73, A_70) | k1_xboole_0=B_73)), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.66/1.32  tff(c_331, plain, (![D_129]: (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))!=k1_xboole_0 | k1_xboole_0=D_129 | ~m2_orders_2(D_129, '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_326, c_50])).
% 2.66/1.32  tff(c_339, plain, (![D_130]: (k1_xboole_0=D_130 | ~m2_orders_2(D_130, '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_331])).
% 2.66/1.32  tff(c_343, plain, ('#skF_3'('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_313, c_339])).
% 2.66/1.32  tff(c_344, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_343, c_313])).
% 2.66/1.32  tff(c_354, plain, (![B_131, A_132, C_133]: (r2_hidden(k1_funct_1(B_131, u1_struct_0(A_132)), C_133) | ~m2_orders_2(C_133, A_132, B_131) | ~m1_orders_1(B_131, k1_orders_1(u1_struct_0(A_132))) | ~l1_orders_2(A_132) | ~v5_orders_2(A_132) | ~v4_orders_2(A_132) | ~v3_orders_2(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.66/1.32  tff(c_6, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.66/1.32  tff(c_199, plain, (![B_91, A_92]: (~r2_hidden(B_91, A_92) | k4_xboole_0(A_92, k1_tarski(B_91))!=A_92)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.66/1.32  tff(c_208, plain, (![B_91]: (~r2_hidden(B_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_199])).
% 2.66/1.32  tff(c_368, plain, (![A_134, B_135]: (~m2_orders_2(k1_xboole_0, A_134, B_135) | ~m1_orders_1(B_135, k1_orders_1(u1_struct_0(A_134))) | ~l1_orders_2(A_134) | ~v5_orders_2(A_134) | ~v4_orders_2(A_134) | ~v3_orders_2(A_134) | v2_struct_0(A_134))), inference(resolution, [status(thm)], [c_354, c_208])).
% 2.66/1.32  tff(c_371, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_58, c_368])).
% 2.66/1.32  tff(c_374, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_344, c_371])).
% 2.66/1.32  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_374])).
% 2.66/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.32  
% 2.66/1.32  Inference rules
% 2.66/1.32  ----------------------
% 2.66/1.32  #Ref     : 0
% 2.66/1.32  #Sup     : 72
% 2.66/1.32  #Fact    : 0
% 2.66/1.32  #Define  : 0
% 2.66/1.32  #Split   : 0
% 2.66/1.32  #Chain   : 0
% 2.66/1.32  #Close   : 0
% 2.66/1.32  
% 2.66/1.32  Ordering : KBO
% 2.66/1.32  
% 2.66/1.32  Simplification rules
% 2.66/1.32  ----------------------
% 2.66/1.32  #Subsume      : 0
% 2.66/1.32  #Demod        : 25
% 2.66/1.32  #Tautology    : 58
% 2.66/1.32  #SimpNegUnit  : 4
% 2.66/1.32  #BackRed      : 1
% 2.66/1.32  
% 2.66/1.32  #Partial instantiations: 0
% 2.66/1.32  #Strategies tried      : 1
% 2.66/1.32  
% 2.66/1.32  Timing (in seconds)
% 2.66/1.32  ----------------------
% 2.66/1.33  Preprocessing        : 0.36
% 2.66/1.33  Parsing              : 0.19
% 2.66/1.33  CNF conversion       : 0.03
% 2.66/1.33  Main loop            : 0.21
% 2.66/1.33  Inferencing          : 0.08
% 2.66/1.33  Reduction            : 0.07
% 2.66/1.33  Demodulation         : 0.05
% 2.66/1.33  BG Simplification    : 0.02
% 2.66/1.33  Subsumption          : 0.03
% 2.66/1.33  Abstraction          : 0.02
% 2.66/1.33  MUC search           : 0.00
% 2.66/1.33  Cooper               : 0.00
% 2.66/1.33  Total                : 0.60
% 2.66/1.33  Index Insertion      : 0.00
% 2.66/1.33  Index Deletion       : 0.00
% 2.66/1.33  Index Matching       : 0.00
% 2.66/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
