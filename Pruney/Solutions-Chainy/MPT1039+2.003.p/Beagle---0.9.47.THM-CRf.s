%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:01 EST 2020

% Result     : Theorem 14.53s
% Output     : CNFRefutation 14.69s
% Verified   : 
% Statistics : Number of formulae       :  155 (1810 expanded)
%              Number of leaves         :   22 ( 595 expanded)
%              Depth                    :   13
%              Number of atoms          :  721 (9935 expanded)
%              Number of equality atoms :   67 (2169 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ~ ( ( B = k1_xboole_0
                 => A = k1_xboole_0 )
                & r1_partfun1(C,D)
                & ! [E] :
                    ( ( v1_funct_1(E)
                      & v1_funct_2(E,A,B)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                   => ~ ( r1_partfun1(C,E)
                        & r1_partfun1(D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_2)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ~ ( ( B = k1_xboole_0
               => A = k1_xboole_0 )
              & r1_partfun1(C,D)
              & ! [E] :
                  ( ( v1_funct_1(E)
                    & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                 => ~ ( v1_partfun1(E,A)
                      & r1_partfun1(C,E)
                      & r1_partfun1(D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_partfun1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ~ ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
          & ! [D] :
              ( ( v1_funct_1(D)
                & v1_funct_2(D,A,B)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ~ r1_partfun1(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_57,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_300,plain,(
    ! [B_80,A_81,C_82,D_83] :
      ( k1_xboole_0 = B_80
      | v1_funct_1('#skF_2'(A_81,B_80,C_82,D_83))
      | ~ r1_partfun1(C_82,D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80)))
      | ~ v1_funct_1(D_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80)))
      | ~ v1_funct_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_306,plain,(
    ! [C_82] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_1('#skF_2'('#skF_3','#skF_4',C_82,'#skF_6'))
      | ~ r1_partfun1(C_82,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_82) ) ),
    inference(resolution,[status(thm)],[c_50,c_300])).

tff(c_313,plain,(
    ! [C_82] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_1('#skF_2'('#skF_3','#skF_4',C_82,'#skF_6'))
      | ~ r1_partfun1(C_82,'#skF_6')
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_306])).

tff(c_319,plain,(
    ! [C_84] :
      ( v1_funct_1('#skF_2'('#skF_3','#skF_4',C_84,'#skF_6'))
      | ~ r1_partfun1(C_84,'#skF_6')
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_84) ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_313])).

tff(c_329,plain,
    ( v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ r1_partfun1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_319])).

tff(c_338,plain,(
    v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_329])).

tff(c_394,plain,(
    ! [B_95,A_96,C_97,D_98] :
      ( k1_xboole_0 = B_95
      | v1_partfun1('#skF_2'(A_96,B_95,C_97,D_98),A_96)
      | ~ r1_partfun1(C_97,D_98)
      | ~ m1_subset_1(D_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95)))
      | ~ v1_funct_1(D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95)))
      | ~ v1_funct_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_400,plain,(
    ! [C_97] :
      ( k1_xboole_0 = '#skF_4'
      | v1_partfun1('#skF_2'('#skF_3','#skF_4',C_97,'#skF_6'),'#skF_3')
      | ~ r1_partfun1(C_97,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_97) ) ),
    inference(resolution,[status(thm)],[c_50,c_394])).

tff(c_407,plain,(
    ! [C_97] :
      ( k1_xboole_0 = '#skF_4'
      | v1_partfun1('#skF_2'('#skF_3','#skF_4',C_97,'#skF_6'),'#skF_3')
      | ~ r1_partfun1(C_97,'#skF_6')
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_400])).

tff(c_413,plain,(
    ! [C_99] :
      ( v1_partfun1('#skF_2'('#skF_3','#skF_4',C_99,'#skF_6'),'#skF_3')
      | ~ r1_partfun1(C_99,'#skF_6')
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_99) ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_407])).

tff(c_423,plain,
    ( v1_partfun1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')
    | ~ r1_partfun1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_413])).

tff(c_432,plain,(
    v1_partfun1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_423])).

tff(c_703,plain,(
    ! [B_122,A_123,C_124,D_125] :
      ( k1_xboole_0 = B_122
      | m1_subset_1('#skF_2'(A_123,B_122,C_124,D_125),k1_zfmisc_1(k2_zfmisc_1(A_123,B_122)))
      | ~ r1_partfun1(C_124,D_125)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_122)))
      | ~ v1_funct_1(D_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_123,B_122)))
      | ~ v1_funct_1(C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_20,plain,(
    ! [B_5,A_4,C_6] :
      ( k1_xboole_0 = B_5
      | v1_funct_1('#skF_1'(A_4,B_5,C_6))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5)))
      | ~ v1_funct_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1027,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( v1_funct_1('#skF_1'(A_158,B_159,'#skF_2'(A_158,B_159,C_160,D_161)))
      | ~ v1_funct_1('#skF_2'(A_158,B_159,C_160,D_161))
      | k1_xboole_0 = B_159
      | ~ r1_partfun1(C_160,D_161)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ v1_funct_1(D_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ v1_funct_1(C_160) ) ),
    inference(resolution,[status(thm)],[c_703,c_20])).

tff(c_1037,plain,(
    ! [C_160] :
      ( v1_funct_1('#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4',C_160,'#skF_6')))
      | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4',C_160,'#skF_6'))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_partfun1(C_160,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_160) ) ),
    inference(resolution,[status(thm)],[c_50,c_1027])).

tff(c_1046,plain,(
    ! [C_160] :
      ( v1_funct_1('#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4',C_160,'#skF_6')))
      | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4',C_160,'#skF_6'))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_partfun1(C_160,'#skF_6')
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1037])).

tff(c_1052,plain,(
    ! [C_162] :
      ( v1_funct_1('#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4',C_162,'#skF_6')))
      | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4',C_162,'#skF_6'))
      | ~ r1_partfun1(C_162,'#skF_6')
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_162) ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_1046])).

tff(c_1066,plain,
    ( v1_funct_1('#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ r1_partfun1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_1052])).

tff(c_1078,plain,(
    v1_funct_1('#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_338,c_1066])).

tff(c_38,plain,(
    ! [B_14,A_13,C_15,D_19] :
      ( k1_xboole_0 = B_14
      | m1_subset_1('#skF_2'(A_13,B_14,C_15,D_19),k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ r1_partfun1(C_15,D_19)
      | ~ m1_subset_1(D_19,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(D_19)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_16,plain,(
    ! [B_5,A_4,C_6] :
      ( k1_xboole_0 = B_5
      | v1_funct_2('#skF_1'(A_4,B_5,C_6),A_4,B_5)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5)))
      | ~ v1_funct_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1191,plain,(
    ! [A_177,B_178,C_179,D_180] :
      ( v1_funct_2('#skF_1'(A_177,B_178,'#skF_2'(A_177,B_178,C_179,D_180)),A_177,B_178)
      | ~ v1_funct_1('#skF_2'(A_177,B_178,C_179,D_180))
      | k1_xboole_0 = B_178
      | ~ r1_partfun1(C_179,D_180)
      | ~ m1_subset_1(D_180,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178)))
      | ~ v1_funct_1(D_180)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178)))
      | ~ v1_funct_1(C_179) ) ),
    inference(resolution,[status(thm)],[c_703,c_16])).

tff(c_162,plain,(
    ! [B_49,A_50,C_51] :
      ( k1_xboole_0 = B_49
      | m1_subset_1('#skF_1'(A_50,B_49,C_51),k1_zfmisc_1(k2_zfmisc_1(A_50,B_49)))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49)))
      | ~ v1_funct_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [B_2,C_3,A_1] :
      ( k1_xboole_0 = B_2
      | v1_partfun1(C_3,A_1)
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_191,plain,(
    ! [A_50,B_49,C_51] :
      ( v1_partfun1('#skF_1'(A_50,B_49,C_51),A_50)
      | ~ v1_funct_2('#skF_1'(A_50,B_49,C_51),A_50,B_49)
      | ~ v1_funct_1('#skF_1'(A_50,B_49,C_51))
      | k1_xboole_0 = B_49
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49)))
      | ~ v1_funct_1(C_51) ) ),
    inference(resolution,[status(thm)],[c_162,c_4])).

tff(c_1580,plain,(
    ! [A_314,B_315,C_316,D_317] :
      ( v1_partfun1('#skF_1'(A_314,B_315,'#skF_2'(A_314,B_315,C_316,D_317)),A_314)
      | ~ v1_funct_1('#skF_1'(A_314,B_315,'#skF_2'(A_314,B_315,C_316,D_317)))
      | ~ m1_subset_1('#skF_2'(A_314,B_315,C_316,D_317),k1_zfmisc_1(k2_zfmisc_1(A_314,B_315)))
      | ~ v1_funct_1('#skF_2'(A_314,B_315,C_316,D_317))
      | k1_xboole_0 = B_315
      | ~ r1_partfun1(C_316,D_317)
      | ~ m1_subset_1(D_317,k1_zfmisc_1(k2_zfmisc_1(A_314,B_315)))
      | ~ v1_funct_1(D_317)
      | ~ m1_subset_1(C_316,k1_zfmisc_1(k2_zfmisc_1(A_314,B_315)))
      | ~ v1_funct_1(C_316) ) ),
    inference(resolution,[status(thm)],[c_1191,c_191])).

tff(c_1585,plain,(
    ! [A_13,B_14,C_15,D_19] :
      ( v1_partfun1('#skF_1'(A_13,B_14,'#skF_2'(A_13,B_14,C_15,D_19)),A_13)
      | ~ v1_funct_1('#skF_1'(A_13,B_14,'#skF_2'(A_13,B_14,C_15,D_19)))
      | ~ v1_funct_1('#skF_2'(A_13,B_14,C_15,D_19))
      | k1_xboole_0 = B_14
      | ~ r1_partfun1(C_15,D_19)
      | ~ m1_subset_1(D_19,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(D_19)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(resolution,[status(thm)],[c_38,c_1580])).

tff(c_12,plain,(
    ! [B_5,A_4,C_6] :
      ( k1_xboole_0 = B_5
      | m1_subset_1('#skF_1'(A_4,B_5,C_6),k1_zfmisc_1(k2_zfmisc_1(A_4,B_5)))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5)))
      | ~ v1_funct_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [B_5,C_6,A_4] :
      ( k1_xboole_0 = B_5
      | r1_partfun1(C_6,'#skF_1'(A_4,B_5,C_6))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5)))
      | ~ v1_funct_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1224,plain,(
    ! [A_200,B_201,C_202,D_203] :
      ( r1_partfun1('#skF_2'(A_200,B_201,C_202,D_203),'#skF_1'(A_200,B_201,'#skF_2'(A_200,B_201,C_202,D_203)))
      | ~ v1_funct_1('#skF_2'(A_200,B_201,C_202,D_203))
      | k1_xboole_0 = B_201
      | ~ r1_partfun1(C_202,D_203)
      | ~ m1_subset_1(D_203,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201)))
      | ~ v1_funct_1(D_203)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201)))
      | ~ v1_funct_1(C_202) ) ),
    inference(resolution,[status(thm)],[c_703,c_8])).

tff(c_22,plain,(
    ! [D_12,C_10,A_8,B_9] :
      ( D_12 = C_10
      | ~ r1_partfun1(C_10,D_12)
      | ~ v1_partfun1(D_12,A_8)
      | ~ v1_partfun1(C_10,A_8)
      | ~ m1_subset_1(D_12,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_1(D_12)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3693,plain,(
    ! [C_487,D_490,A_491,B_486,B_489,A_488] :
      ( '#skF_1'(A_491,B_486,'#skF_2'(A_491,B_486,C_487,D_490)) = '#skF_2'(A_491,B_486,C_487,D_490)
      | ~ v1_partfun1('#skF_1'(A_491,B_486,'#skF_2'(A_491,B_486,C_487,D_490)),A_488)
      | ~ v1_partfun1('#skF_2'(A_491,B_486,C_487,D_490),A_488)
      | ~ m1_subset_1('#skF_1'(A_491,B_486,'#skF_2'(A_491,B_486,C_487,D_490)),k1_zfmisc_1(k2_zfmisc_1(A_488,B_489)))
      | ~ v1_funct_1('#skF_1'(A_491,B_486,'#skF_2'(A_491,B_486,C_487,D_490)))
      | ~ m1_subset_1('#skF_2'(A_491,B_486,C_487,D_490),k1_zfmisc_1(k2_zfmisc_1(A_488,B_489)))
      | ~ v1_funct_1('#skF_2'(A_491,B_486,C_487,D_490))
      | k1_xboole_0 = B_486
      | ~ r1_partfun1(C_487,D_490)
      | ~ m1_subset_1(D_490,k1_zfmisc_1(k2_zfmisc_1(A_491,B_486)))
      | ~ v1_funct_1(D_490)
      | ~ m1_subset_1(C_487,k1_zfmisc_1(k2_zfmisc_1(A_491,B_486)))
      | ~ v1_funct_1(C_487) ) ),
    inference(resolution,[status(thm)],[c_1224,c_22])).

tff(c_9381,plain,(
    ! [A_710,B_711,C_712,D_713] :
      ( '#skF_1'(A_710,B_711,'#skF_2'(A_710,B_711,C_712,D_713)) = '#skF_2'(A_710,B_711,C_712,D_713)
      | ~ v1_partfun1('#skF_1'(A_710,B_711,'#skF_2'(A_710,B_711,C_712,D_713)),A_710)
      | ~ v1_partfun1('#skF_2'(A_710,B_711,C_712,D_713),A_710)
      | ~ v1_funct_1('#skF_1'(A_710,B_711,'#skF_2'(A_710,B_711,C_712,D_713)))
      | ~ r1_partfun1(C_712,D_713)
      | ~ m1_subset_1(D_713,k1_zfmisc_1(k2_zfmisc_1(A_710,B_711)))
      | ~ v1_funct_1(D_713)
      | ~ m1_subset_1(C_712,k1_zfmisc_1(k2_zfmisc_1(A_710,B_711)))
      | ~ v1_funct_1(C_712)
      | k1_xboole_0 = B_711
      | ~ m1_subset_1('#skF_2'(A_710,B_711,C_712,D_713),k1_zfmisc_1(k2_zfmisc_1(A_710,B_711)))
      | ~ v1_funct_1('#skF_2'(A_710,B_711,C_712,D_713)) ) ),
    inference(resolution,[status(thm)],[c_12,c_3693])).

tff(c_9453,plain,(
    ! [A_715,B_716,C_717,D_718] :
      ( '#skF_1'(A_715,B_716,'#skF_2'(A_715,B_716,C_717,D_718)) = '#skF_2'(A_715,B_716,C_717,D_718)
      | ~ v1_partfun1('#skF_2'(A_715,B_716,C_717,D_718),A_715)
      | ~ m1_subset_1('#skF_2'(A_715,B_716,C_717,D_718),k1_zfmisc_1(k2_zfmisc_1(A_715,B_716)))
      | ~ v1_funct_1('#skF_1'(A_715,B_716,'#skF_2'(A_715,B_716,C_717,D_718)))
      | ~ v1_funct_1('#skF_2'(A_715,B_716,C_717,D_718))
      | k1_xboole_0 = B_716
      | ~ r1_partfun1(C_717,D_718)
      | ~ m1_subset_1(D_718,k1_zfmisc_1(k2_zfmisc_1(A_715,B_716)))
      | ~ v1_funct_1(D_718)
      | ~ m1_subset_1(C_717,k1_zfmisc_1(k2_zfmisc_1(A_715,B_716)))
      | ~ v1_funct_1(C_717) ) ),
    inference(resolution,[status(thm)],[c_1585,c_9381])).

tff(c_9492,plain,(
    ! [A_719,B_720,C_721,D_722] :
      ( '#skF_1'(A_719,B_720,'#skF_2'(A_719,B_720,C_721,D_722)) = '#skF_2'(A_719,B_720,C_721,D_722)
      | ~ v1_partfun1('#skF_2'(A_719,B_720,C_721,D_722),A_719)
      | ~ v1_funct_1('#skF_1'(A_719,B_720,'#skF_2'(A_719,B_720,C_721,D_722)))
      | ~ v1_funct_1('#skF_2'(A_719,B_720,C_721,D_722))
      | k1_xboole_0 = B_720
      | ~ r1_partfun1(C_721,D_722)
      | ~ m1_subset_1(D_722,k1_zfmisc_1(k2_zfmisc_1(A_719,B_720)))
      | ~ v1_funct_1(D_722)
      | ~ m1_subset_1(C_721,k1_zfmisc_1(k2_zfmisc_1(A_719,B_720)))
      | ~ v1_funct_1(C_721) ) ),
    inference(resolution,[status(thm)],[c_38,c_9453])).

tff(c_9526,plain,
    ( '#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ v1_partfun1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_4'
    | ~ r1_partfun1('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1078,c_9492])).

tff(c_9569,plain,
    ( '#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_46,c_338,c_432,c_9526])).

tff(c_9570,plain,(
    '#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_9569])).

tff(c_561,plain,(
    ! [B_109,C_110,A_111,D_112] :
      ( k1_xboole_0 = B_109
      | r1_partfun1(C_110,'#skF_2'(A_111,B_109,C_110,D_112))
      | ~ r1_partfun1(C_110,D_112)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_111,B_109)))
      | ~ v1_funct_1(D_112)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_109)))
      | ~ v1_funct_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_567,plain,(
    ! [C_110] :
      ( k1_xboole_0 = '#skF_4'
      | r1_partfun1(C_110,'#skF_2'('#skF_3','#skF_4',C_110,'#skF_6'))
      | ~ r1_partfun1(C_110,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_110) ) ),
    inference(resolution,[status(thm)],[c_50,c_561])).

tff(c_574,plain,(
    ! [C_110] :
      ( k1_xboole_0 = '#skF_4'
      | r1_partfun1(C_110,'#skF_2'('#skF_3','#skF_4',C_110,'#skF_6'))
      | ~ r1_partfun1(C_110,'#skF_6')
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_567])).

tff(c_639,plain,(
    ! [C_116] :
      ( r1_partfun1(C_116,'#skF_2'('#skF_3','#skF_4',C_116,'#skF_6'))
      | ~ r1_partfun1(C_116,'#skF_6')
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_116) ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_574])).

tff(c_646,plain,
    ( r1_partfun1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ r1_partfun1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_639])).

tff(c_655,plain,(
    r1_partfun1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_646])).

tff(c_475,plain,(
    ! [B_102,D_103,A_104,C_105] :
      ( k1_xboole_0 = B_102
      | r1_partfun1(D_103,'#skF_2'(A_104,B_102,C_105,D_103))
      | ~ r1_partfun1(C_105,D_103)
      | ~ m1_subset_1(D_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_102)))
      | ~ v1_funct_1(D_103)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_104,B_102)))
      | ~ v1_funct_1(C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_481,plain,(
    ! [C_105] :
      ( k1_xboole_0 = '#skF_4'
      | r1_partfun1('#skF_6','#skF_2'('#skF_3','#skF_4',C_105,'#skF_6'))
      | ~ r1_partfun1(C_105,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_105) ) ),
    inference(resolution,[status(thm)],[c_50,c_475])).

tff(c_488,plain,(
    ! [C_105] :
      ( k1_xboole_0 = '#skF_4'
      | r1_partfun1('#skF_6','#skF_2'('#skF_3','#skF_4',C_105,'#skF_6'))
      | ~ r1_partfun1(C_105,'#skF_6')
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_481])).

tff(c_494,plain,(
    ! [C_106] :
      ( r1_partfun1('#skF_6','#skF_2'('#skF_3','#skF_4',C_106,'#skF_6'))
      | ~ r1_partfun1(C_106,'#skF_6')
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_106) ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_488])).

tff(c_504,plain,
    ( r1_partfun1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ r1_partfun1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_494])).

tff(c_513,plain,(
    r1_partfun1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_504])).

tff(c_843,plain,(
    ! [A_123,B_122,C_124,D_125] :
      ( v1_funct_2('#skF_1'(A_123,B_122,'#skF_2'(A_123,B_122,C_124,D_125)),A_123,B_122)
      | ~ v1_funct_1('#skF_2'(A_123,B_122,C_124,D_125))
      | k1_xboole_0 = B_122
      | ~ r1_partfun1(C_124,D_125)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_122)))
      | ~ v1_funct_1(D_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_123,B_122)))
      | ~ v1_funct_1(C_124) ) ),
    inference(resolution,[status(thm)],[c_703,c_16])).

tff(c_44,plain,(
    ! [E_25] :
      ( ~ r1_partfun1('#skF_6',E_25)
      | ~ r1_partfun1('#skF_5',E_25)
      | ~ m1_subset_1(E_25,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2(E_25,'#skF_3','#skF_4')
      | ~ v1_funct_1(E_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_183,plain,(
    ! [C_51] :
      ( ~ r1_partfun1('#skF_6','#skF_1'('#skF_3','#skF_4',C_51))
      | ~ r1_partfun1('#skF_5','#skF_1'('#skF_3','#skF_4',C_51))
      | ~ v1_funct_2('#skF_1'('#skF_3','#skF_4',C_51),'#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_1'('#skF_3','#skF_4',C_51))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_51) ) ),
    inference(resolution,[status(thm)],[c_162,c_44])).

tff(c_199,plain,(
    ! [C_51] :
      ( ~ r1_partfun1('#skF_6','#skF_1'('#skF_3','#skF_4',C_51))
      | ~ r1_partfun1('#skF_5','#skF_1'('#skF_3','#skF_4',C_51))
      | ~ v1_funct_2('#skF_1'('#skF_3','#skF_4',C_51),'#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_1'('#skF_3','#skF_4',C_51))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_51) ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_183])).

tff(c_767,plain,(
    ! [C_124,D_125] :
      ( ~ r1_partfun1('#skF_6','#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4',C_124,D_125)))
      | ~ r1_partfun1('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4',C_124,D_125)))
      | ~ v1_funct_2('#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4',C_124,D_125)),'#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4',C_124,D_125)))
      | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4',C_124,D_125))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_partfun1(C_124,D_125)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(D_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_124) ) ),
    inference(resolution,[status(thm)],[c_703,c_199])).

tff(c_1604,plain,(
    ! [C_361,D_362] :
      ( ~ r1_partfun1('#skF_6','#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4',C_361,D_362)))
      | ~ r1_partfun1('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4',C_361,D_362)))
      | ~ v1_funct_2('#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4',C_361,D_362)),'#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4',C_361,D_362)))
      | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4',C_361,D_362))
      | ~ r1_partfun1(C_361,D_362)
      | ~ m1_subset_1(D_362,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(D_362)
      | ~ m1_subset_1(C_361,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_361) ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_767])).

tff(c_1608,plain,(
    ! [C_124,D_125] :
      ( ~ r1_partfun1('#skF_6','#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4',C_124,D_125)))
      | ~ r1_partfun1('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4',C_124,D_125)))
      | ~ v1_funct_1('#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4',C_124,D_125)))
      | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4',C_124,D_125))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_partfun1(C_124,D_125)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(D_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_124) ) ),
    inference(resolution,[status(thm)],[c_843,c_1604])).

tff(c_1611,plain,(
    ! [C_124,D_125] :
      ( ~ r1_partfun1('#skF_6','#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4',C_124,D_125)))
      | ~ r1_partfun1('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4',C_124,D_125)))
      | ~ v1_funct_1('#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4',C_124,D_125)))
      | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4',C_124,D_125))
      | ~ r1_partfun1(C_124,D_125)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(D_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(C_124) ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_1608])).

tff(c_9652,plain,
    ( ~ r1_partfun1('#skF_6','#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6')))
    | ~ r1_partfun1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ v1_funct_1('#skF_1'('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ r1_partfun1('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9570,c_1611])).

tff(c_9874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_46,c_338,c_338,c_9570,c_655,c_513,c_9570,c_9652])).

tff(c_9876,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_9875,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_9881,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9876,c_9875])).

tff(c_9890,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9881,c_54])).

tff(c_9891,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9881,c_50])).

tff(c_40,plain,(
    ! [B_14,C_15,D_19] :
      ( v1_funct_1('#skF_2'(k1_xboole_0,B_14,C_15,D_19))
      | ~ r1_partfun1(C_15,D_19)
      | ~ m1_subset_1(D_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14)))
      | ~ v1_funct_1(D_19)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10156,plain,(
    ! [B_757,C_758,D_759] :
      ( v1_funct_1('#skF_2'('#skF_4',B_757,C_758,D_759))
      | ~ r1_partfun1(C_758,D_759)
      | ~ m1_subset_1(D_759,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_757)))
      | ~ v1_funct_1(D_759)
      | ~ m1_subset_1(C_758,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_757)))
      | ~ v1_funct_1(C_758) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9876,c_9876,c_9876,c_40])).

tff(c_10163,plain,(
    ! [C_758] :
      ( v1_funct_1('#skF_2'('#skF_4','#skF_4',C_758,'#skF_6'))
      | ~ r1_partfun1(C_758,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_758,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_1(C_758) ) ),
    inference(resolution,[status(thm)],[c_9891,c_10156])).

tff(c_10174,plain,(
    ! [C_760] :
      ( v1_funct_1('#skF_2'('#skF_4','#skF_4',C_760,'#skF_6'))
      | ~ r1_partfun1(C_760,'#skF_6')
      | ~ m1_subset_1(C_760,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_1(C_760) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_10163])).

tff(c_10188,plain,
    ( v1_funct_1('#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6'))
    | ~ r1_partfun1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_9890,c_10174])).

tff(c_10197,plain,(
    v1_funct_1('#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_10188])).

tff(c_32,plain,(
    ! [B_14,C_15,D_19] :
      ( v1_partfun1('#skF_2'(k1_xboole_0,B_14,C_15,D_19),k1_xboole_0)
      | ~ r1_partfun1(C_15,D_19)
      | ~ m1_subset_1(D_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14)))
      | ~ v1_funct_1(D_19)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10392,plain,(
    ! [B_779,C_780,D_781] :
      ( v1_partfun1('#skF_2'('#skF_4',B_779,C_780,D_781),'#skF_4')
      | ~ r1_partfun1(C_780,D_781)
      | ~ m1_subset_1(D_781,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_779)))
      | ~ v1_funct_1(D_781)
      | ~ m1_subset_1(C_780,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_779)))
      | ~ v1_funct_1(C_780) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9876,c_9876,c_9876,c_9876,c_32])).

tff(c_10399,plain,(
    ! [C_780] :
      ( v1_partfun1('#skF_2'('#skF_4','#skF_4',C_780,'#skF_6'),'#skF_4')
      | ~ r1_partfun1(C_780,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_780,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_1(C_780) ) ),
    inference(resolution,[status(thm)],[c_9891,c_10392])).

tff(c_10410,plain,(
    ! [C_782] :
      ( v1_partfun1('#skF_2'('#skF_4','#skF_4',C_782,'#skF_6'),'#skF_4')
      | ~ r1_partfun1(C_782,'#skF_6')
      | ~ m1_subset_1(C_782,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_1(C_782) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_10399])).

tff(c_10424,plain,
    ( v1_partfun1('#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ r1_partfun1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_9890,c_10410])).

tff(c_10433,plain,(
    v1_partfun1('#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_10424])).

tff(c_36,plain,(
    ! [B_14,C_15,D_19] :
      ( m1_subset_1('#skF_2'(k1_xboole_0,B_14,C_15,D_19),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14)))
      | ~ r1_partfun1(C_15,D_19)
      | ~ m1_subset_1(D_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14)))
      | ~ v1_funct_1(D_19)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10642,plain,(
    ! [B_816,C_817,D_818] :
      ( m1_subset_1('#skF_2'('#skF_4',B_816,C_817,D_818),k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_816)))
      | ~ r1_partfun1(C_817,D_818)
      | ~ m1_subset_1(D_818,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_816)))
      | ~ v1_funct_1(D_818)
      | ~ m1_subset_1(C_817,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_816)))
      | ~ v1_funct_1(C_817) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9876,c_9876,c_9876,c_9876,c_36])).

tff(c_18,plain,(
    ! [B_5,C_6] :
      ( v1_funct_1('#skF_1'(k1_xboole_0,B_5,C_6))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5)))
      | ~ v1_funct_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_9892,plain,(
    ! [B_5,C_6] :
      ( v1_funct_1('#skF_1'('#skF_4',B_5,C_6))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_5)))
      | ~ v1_funct_1(C_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9876,c_9876,c_18])).

tff(c_10941,plain,(
    ! [B_834,C_835,D_836] :
      ( v1_funct_1('#skF_1'('#skF_4',B_834,'#skF_2'('#skF_4',B_834,C_835,D_836)))
      | ~ v1_funct_1('#skF_2'('#skF_4',B_834,C_835,D_836))
      | ~ r1_partfun1(C_835,D_836)
      | ~ m1_subset_1(D_836,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_834)))
      | ~ v1_funct_1(D_836)
      | ~ m1_subset_1(C_835,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_834)))
      | ~ v1_funct_1(C_835) ) ),
    inference(resolution,[status(thm)],[c_10642,c_9892])).

tff(c_10953,plain,(
    ! [C_835] :
      ( v1_funct_1('#skF_1'('#skF_4','#skF_4','#skF_2'('#skF_4','#skF_4',C_835,'#skF_6')))
      | ~ v1_funct_1('#skF_2'('#skF_4','#skF_4',C_835,'#skF_6'))
      | ~ r1_partfun1(C_835,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_835,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_1(C_835) ) ),
    inference(resolution,[status(thm)],[c_9891,c_10941])).

tff(c_10966,plain,(
    ! [C_837] :
      ( v1_funct_1('#skF_1'('#skF_4','#skF_4','#skF_2'('#skF_4','#skF_4',C_837,'#skF_6')))
      | ~ v1_funct_1('#skF_2'('#skF_4','#skF_4',C_837,'#skF_6'))
      | ~ r1_partfun1(C_837,'#skF_6')
      | ~ m1_subset_1(C_837,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_1(C_837) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_10953])).

tff(c_10988,plain,
    ( v1_funct_1('#skF_1'('#skF_4','#skF_4','#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6'))
    | ~ r1_partfun1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_9890,c_10966])).

tff(c_11000,plain,(
    v1_funct_1('#skF_1'('#skF_4','#skF_4','#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_10197,c_10988])).

tff(c_10641,plain,(
    ! [B_14,C_15,D_19] :
      ( m1_subset_1('#skF_2'('#skF_4',B_14,C_15,D_19),k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_14)))
      | ~ r1_partfun1(C_15,D_19)
      | ~ m1_subset_1(D_19,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_14)))
      | ~ v1_funct_1(D_19)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9876,c_9876,c_9876,c_9876,c_36])).

tff(c_14,plain,(
    ! [B_5,C_6] :
      ( v1_funct_2('#skF_1'(k1_xboole_0,B_5,C_6),k1_xboole_0,B_5)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5)))
      | ~ v1_funct_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_9948,plain,(
    ! [B_5,C_6] :
      ( v1_funct_2('#skF_1'('#skF_4',B_5,C_6),'#skF_4',B_5)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_5)))
      | ~ v1_funct_1(C_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9876,c_9876,c_9876,c_14])).

tff(c_11196,plain,(
    ! [B_859,C_860,D_861] :
      ( v1_funct_2('#skF_1'('#skF_4',B_859,'#skF_2'('#skF_4',B_859,C_860,D_861)),'#skF_4',B_859)
      | ~ v1_funct_1('#skF_2'('#skF_4',B_859,C_860,D_861))
      | ~ r1_partfun1(C_860,D_861)
      | ~ m1_subset_1(D_861,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_859)))
      | ~ v1_funct_1(D_861)
      | ~ m1_subset_1(C_860,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_859)))
      | ~ v1_funct_1(C_860) ) ),
    inference(resolution,[status(thm)],[c_10642,c_9948])).

tff(c_10,plain,(
    ! [B_5,C_6] :
      ( m1_subset_1('#skF_1'(k1_xboole_0,B_5,C_6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5)))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5)))
      | ~ v1_funct_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10005,plain,(
    ! [B_741,C_742] :
      ( m1_subset_1('#skF_1'('#skF_4',B_741,C_742),k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_741)))
      | ~ m1_subset_1(C_742,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_741)))
      | ~ v1_funct_1(C_742) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9876,c_9876,c_9876,c_10])).

tff(c_2,plain,(
    ! [C_3,B_2] :
      ( v1_partfun1(C_3,k1_xboole_0)
      | ~ v1_funct_2(C_3,k1_xboole_0,B_2)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_9934,plain,(
    ! [C_3,B_2] :
      ( v1_partfun1(C_3,'#skF_4')
      | ~ v1_funct_2(C_3,'#skF_4',B_2)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_2)))
      | ~ v1_funct_1(C_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9876,c_9876,c_9876,c_2])).

tff(c_10031,plain,(
    ! [B_741,C_742] :
      ( v1_partfun1('#skF_1'('#skF_4',B_741,C_742),'#skF_4')
      | ~ v1_funct_2('#skF_1'('#skF_4',B_741,C_742),'#skF_4',B_741)
      | ~ v1_funct_1('#skF_1'('#skF_4',B_741,C_742))
      | ~ m1_subset_1(C_742,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_741)))
      | ~ v1_funct_1(C_742) ) ),
    inference(resolution,[status(thm)],[c_10005,c_9934])).

tff(c_11790,plain,(
    ! [B_1001,C_1002,D_1003] :
      ( v1_partfun1('#skF_1'('#skF_4',B_1001,'#skF_2'('#skF_4',B_1001,C_1002,D_1003)),'#skF_4')
      | ~ v1_funct_1('#skF_1'('#skF_4',B_1001,'#skF_2'('#skF_4',B_1001,C_1002,D_1003)))
      | ~ m1_subset_1('#skF_2'('#skF_4',B_1001,C_1002,D_1003),k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_1001)))
      | ~ v1_funct_1('#skF_2'('#skF_4',B_1001,C_1002,D_1003))
      | ~ r1_partfun1(C_1002,D_1003)
      | ~ m1_subset_1(D_1003,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_1001)))
      | ~ v1_funct_1(D_1003)
      | ~ m1_subset_1(C_1002,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_1001)))
      | ~ v1_funct_1(C_1002) ) ),
    inference(resolution,[status(thm)],[c_11196,c_10031])).

tff(c_11799,plain,(
    ! [B_14,C_15,D_19] :
      ( v1_partfun1('#skF_1'('#skF_4',B_14,'#skF_2'('#skF_4',B_14,C_15,D_19)),'#skF_4')
      | ~ v1_funct_1('#skF_1'('#skF_4',B_14,'#skF_2'('#skF_4',B_14,C_15,D_19)))
      | ~ v1_funct_1('#skF_2'('#skF_4',B_14,C_15,D_19))
      | ~ r1_partfun1(C_15,D_19)
      | ~ m1_subset_1(D_19,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_14)))
      | ~ v1_funct_1(D_19)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(resolution,[status(thm)],[c_10641,c_11790])).

tff(c_10004,plain,(
    ! [B_5,C_6] :
      ( m1_subset_1('#skF_1'('#skF_4',B_5,C_6),k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_5)))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_5)))
      | ~ v1_funct_1(C_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9876,c_9876,c_9876,c_10])).

tff(c_6,plain,(
    ! [C_6,B_5] :
      ( r1_partfun1(C_6,'#skF_1'(k1_xboole_0,B_5,C_6))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5)))
      | ~ v1_funct_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_9906,plain,(
    ! [C_6,B_5] :
      ( r1_partfun1(C_6,'#skF_1'('#skF_4',B_5,C_6))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_5)))
      | ~ v1_funct_1(C_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9876,c_9876,c_6])).

tff(c_11251,plain,(
    ! [B_877,C_878,D_879] :
      ( r1_partfun1('#skF_2'('#skF_4',B_877,C_878,D_879),'#skF_1'('#skF_4',B_877,'#skF_2'('#skF_4',B_877,C_878,D_879)))
      | ~ v1_funct_1('#skF_2'('#skF_4',B_877,C_878,D_879))
      | ~ r1_partfun1(C_878,D_879)
      | ~ m1_subset_1(D_879,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_877)))
      | ~ v1_funct_1(D_879)
      | ~ m1_subset_1(C_878,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_877)))
      | ~ v1_funct_1(C_878) ) ),
    inference(resolution,[status(thm)],[c_10642,c_9906])).

tff(c_13677,plain,(
    ! [D_1169,B_1167,C_1165,B_1168,A_1166] :
      ( '#skF_1'('#skF_4',B_1168,'#skF_2'('#skF_4',B_1168,C_1165,D_1169)) = '#skF_2'('#skF_4',B_1168,C_1165,D_1169)
      | ~ v1_partfun1('#skF_1'('#skF_4',B_1168,'#skF_2'('#skF_4',B_1168,C_1165,D_1169)),A_1166)
      | ~ v1_partfun1('#skF_2'('#skF_4',B_1168,C_1165,D_1169),A_1166)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_1168,'#skF_2'('#skF_4',B_1168,C_1165,D_1169)),k1_zfmisc_1(k2_zfmisc_1(A_1166,B_1167)))
      | ~ v1_funct_1('#skF_1'('#skF_4',B_1168,'#skF_2'('#skF_4',B_1168,C_1165,D_1169)))
      | ~ m1_subset_1('#skF_2'('#skF_4',B_1168,C_1165,D_1169),k1_zfmisc_1(k2_zfmisc_1(A_1166,B_1167)))
      | ~ v1_funct_1('#skF_2'('#skF_4',B_1168,C_1165,D_1169))
      | ~ r1_partfun1(C_1165,D_1169)
      | ~ m1_subset_1(D_1169,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_1168)))
      | ~ v1_funct_1(D_1169)
      | ~ m1_subset_1(C_1165,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_1168)))
      | ~ v1_funct_1(C_1165) ) ),
    inference(resolution,[status(thm)],[c_11251,c_22])).

tff(c_18697,plain,(
    ! [B_1313,C_1314,D_1315] :
      ( '#skF_1'('#skF_4',B_1313,'#skF_2'('#skF_4',B_1313,C_1314,D_1315)) = '#skF_2'('#skF_4',B_1313,C_1314,D_1315)
      | ~ v1_partfun1('#skF_1'('#skF_4',B_1313,'#skF_2'('#skF_4',B_1313,C_1314,D_1315)),'#skF_4')
      | ~ v1_partfun1('#skF_2'('#skF_4',B_1313,C_1314,D_1315),'#skF_4')
      | ~ v1_funct_1('#skF_1'('#skF_4',B_1313,'#skF_2'('#skF_4',B_1313,C_1314,D_1315)))
      | ~ r1_partfun1(C_1314,D_1315)
      | ~ m1_subset_1(D_1315,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_1313)))
      | ~ v1_funct_1(D_1315)
      | ~ m1_subset_1(C_1314,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_1313)))
      | ~ v1_funct_1(C_1314)
      | ~ m1_subset_1('#skF_2'('#skF_4',B_1313,C_1314,D_1315),k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_1313)))
      | ~ v1_funct_1('#skF_2'('#skF_4',B_1313,C_1314,D_1315)) ) ),
    inference(resolution,[status(thm)],[c_10004,c_13677])).

tff(c_19427,plain,(
    ! [B_1341,C_1342,D_1343] :
      ( '#skF_1'('#skF_4',B_1341,'#skF_2'('#skF_4',B_1341,C_1342,D_1343)) = '#skF_2'('#skF_4',B_1341,C_1342,D_1343)
      | ~ v1_partfun1('#skF_1'('#skF_4',B_1341,'#skF_2'('#skF_4',B_1341,C_1342,D_1343)),'#skF_4')
      | ~ v1_partfun1('#skF_2'('#skF_4',B_1341,C_1342,D_1343),'#skF_4')
      | ~ v1_funct_1('#skF_1'('#skF_4',B_1341,'#skF_2'('#skF_4',B_1341,C_1342,D_1343)))
      | ~ v1_funct_1('#skF_2'('#skF_4',B_1341,C_1342,D_1343))
      | ~ r1_partfun1(C_1342,D_1343)
      | ~ m1_subset_1(D_1343,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_1341)))
      | ~ v1_funct_1(D_1343)
      | ~ m1_subset_1(C_1342,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_1341)))
      | ~ v1_funct_1(C_1342) ) ),
    inference(resolution,[status(thm)],[c_10641,c_18697])).

tff(c_19457,plain,(
    ! [B_1344,C_1345,D_1346] :
      ( '#skF_1'('#skF_4',B_1344,'#skF_2'('#skF_4',B_1344,C_1345,D_1346)) = '#skF_2'('#skF_4',B_1344,C_1345,D_1346)
      | ~ v1_partfun1('#skF_2'('#skF_4',B_1344,C_1345,D_1346),'#skF_4')
      | ~ v1_funct_1('#skF_1'('#skF_4',B_1344,'#skF_2'('#skF_4',B_1344,C_1345,D_1346)))
      | ~ v1_funct_1('#skF_2'('#skF_4',B_1344,C_1345,D_1346))
      | ~ r1_partfun1(C_1345,D_1346)
      | ~ m1_subset_1(D_1346,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_1344)))
      | ~ v1_funct_1(D_1346)
      | ~ m1_subset_1(C_1345,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_1344)))
      | ~ v1_funct_1(C_1345) ) ),
    inference(resolution,[status(thm)],[c_11799,c_19427])).

tff(c_19489,plain,
    ( '#skF_1'('#skF_4','#skF_4','#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6')) = '#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6')
    | ~ v1_partfun1('#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ v1_funct_1('#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6'))
    | ~ r1_partfun1('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_11000,c_19457])).

tff(c_19522,plain,(
    '#skF_1'('#skF_4','#skF_4','#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6')) = '#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_9890,c_52,c_9891,c_46,c_10197,c_10433,c_19489])).

tff(c_28,plain,(
    ! [C_15,B_14,D_19] :
      ( r1_partfun1(C_15,'#skF_2'(k1_xboole_0,B_14,C_15,D_19))
      | ~ r1_partfun1(C_15,D_19)
      | ~ m1_subset_1(D_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14)))
      | ~ v1_funct_1(D_19)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10226,plain,(
    ! [C_762,B_763,D_764] :
      ( r1_partfun1(C_762,'#skF_2'('#skF_4',B_763,C_762,D_764))
      | ~ r1_partfun1(C_762,D_764)
      | ~ m1_subset_1(D_764,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_763)))
      | ~ v1_funct_1(D_764)
      | ~ m1_subset_1(C_762,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_763)))
      | ~ v1_funct_1(C_762) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9876,c_9876,c_9876,c_28])).

tff(c_10233,plain,(
    ! [C_762] :
      ( r1_partfun1(C_762,'#skF_2'('#skF_4','#skF_4',C_762,'#skF_6'))
      | ~ r1_partfun1(C_762,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_762,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_1(C_762) ) ),
    inference(resolution,[status(thm)],[c_9891,c_10226])).

tff(c_10244,plain,(
    ! [C_765] :
      ( r1_partfun1(C_765,'#skF_2'('#skF_4','#skF_4',C_765,'#skF_6'))
      | ~ r1_partfun1(C_765,'#skF_6')
      | ~ m1_subset_1(C_765,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_1(C_765) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_10233])).

tff(c_10254,plain,
    ( r1_partfun1('#skF_5','#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6'))
    | ~ r1_partfun1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_9890,c_10244])).

tff(c_10263,plain,(
    r1_partfun1('#skF_5','#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_10254])).

tff(c_24,plain,(
    ! [D_19,B_14,C_15] :
      ( r1_partfun1(D_19,'#skF_2'(k1_xboole_0,B_14,C_15,D_19))
      | ~ r1_partfun1(C_15,D_19)
      | ~ m1_subset_1(D_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14)))
      | ~ v1_funct_1(D_19)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10292,plain,(
    ! [D_770,B_771,C_772] :
      ( r1_partfun1(D_770,'#skF_2'('#skF_4',B_771,C_772,D_770))
      | ~ r1_partfun1(C_772,D_770)
      | ~ m1_subset_1(D_770,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_771)))
      | ~ v1_funct_1(D_770)
      | ~ m1_subset_1(C_772,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_771)))
      | ~ v1_funct_1(C_772) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9876,c_9876,c_9876,c_24])).

tff(c_10299,plain,(
    ! [C_772] :
      ( r1_partfun1('#skF_6','#skF_2'('#skF_4','#skF_4',C_772,'#skF_6'))
      | ~ r1_partfun1(C_772,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_772,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_1(C_772) ) ),
    inference(resolution,[status(thm)],[c_9891,c_10292])).

tff(c_10310,plain,(
    ! [C_773] :
      ( r1_partfun1('#skF_6','#skF_2'('#skF_4','#skF_4',C_773,'#skF_6'))
      | ~ r1_partfun1(C_773,'#skF_6')
      | ~ m1_subset_1(C_773,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_1(C_773) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_10299])).

tff(c_10324,plain,
    ( r1_partfun1('#skF_6','#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6'))
    | ~ r1_partfun1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_9890,c_10310])).

tff(c_10333,plain,(
    r1_partfun1('#skF_6','#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_10324])).

tff(c_9918,plain,(
    ! [E_25] :
      ( ~ r1_partfun1('#skF_6',E_25)
      | ~ r1_partfun1('#skF_5',E_25)
      | ~ m1_subset_1(E_25,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_2(E_25,'#skF_4','#skF_4')
      | ~ v1_funct_1(E_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9881,c_9881,c_44])).

tff(c_10032,plain,(
    ! [C_742] :
      ( ~ r1_partfun1('#skF_6','#skF_1'('#skF_4','#skF_4',C_742))
      | ~ r1_partfun1('#skF_5','#skF_1'('#skF_4','#skF_4',C_742))
      | ~ v1_funct_2('#skF_1'('#skF_4','#skF_4',C_742),'#skF_4','#skF_4')
      | ~ v1_funct_1('#skF_1'('#skF_4','#skF_4',C_742))
      | ~ m1_subset_1(C_742,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_1(C_742) ) ),
    inference(resolution,[status(thm)],[c_10005,c_9918])).

tff(c_10748,plain,(
    ! [C_817,D_818] :
      ( ~ r1_partfun1('#skF_6','#skF_1'('#skF_4','#skF_4','#skF_2'('#skF_4','#skF_4',C_817,D_818)))
      | ~ r1_partfun1('#skF_5','#skF_1'('#skF_4','#skF_4','#skF_2'('#skF_4','#skF_4',C_817,D_818)))
      | ~ v1_funct_2('#skF_1'('#skF_4','#skF_4','#skF_2'('#skF_4','#skF_4',C_817,D_818)),'#skF_4','#skF_4')
      | ~ v1_funct_1('#skF_1'('#skF_4','#skF_4','#skF_2'('#skF_4','#skF_4',C_817,D_818)))
      | ~ v1_funct_1('#skF_2'('#skF_4','#skF_4',C_817,D_818))
      | ~ r1_partfun1(C_817,D_818)
      | ~ m1_subset_1(D_818,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_1(D_818)
      | ~ m1_subset_1(C_817,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_1(C_817) ) ),
    inference(resolution,[status(thm)],[c_10642,c_10032])).

tff(c_11205,plain,(
    ! [C_860,D_861] :
      ( ~ r1_partfun1('#skF_6','#skF_1'('#skF_4','#skF_4','#skF_2'('#skF_4','#skF_4',C_860,D_861)))
      | ~ r1_partfun1('#skF_5','#skF_1'('#skF_4','#skF_4','#skF_2'('#skF_4','#skF_4',C_860,D_861)))
      | ~ v1_funct_1('#skF_1'('#skF_4','#skF_4','#skF_2'('#skF_4','#skF_4',C_860,D_861)))
      | ~ v1_funct_1('#skF_2'('#skF_4','#skF_4',C_860,D_861))
      | ~ r1_partfun1(C_860,D_861)
      | ~ m1_subset_1(D_861,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_1(D_861)
      | ~ m1_subset_1(C_860,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_1(C_860) ) ),
    inference(resolution,[status(thm)],[c_11196,c_10748])).

tff(c_19690,plain,
    ( ~ r1_partfun1('#skF_6','#skF_1'('#skF_4','#skF_4','#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6')))
    | ~ r1_partfun1('#skF_5','#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6'))
    | ~ v1_funct_1('#skF_1'('#skF_4','#skF_4','#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_2'('#skF_4','#skF_4','#skF_5','#skF_6'))
    | ~ r1_partfun1('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_19522,c_11205])).

tff(c_19990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_9890,c_52,c_9891,c_46,c_10197,c_10197,c_19522,c_10263,c_10333,c_19522,c_19690])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.53/6.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.58/6.50  
% 14.58/6.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.58/6.51  %$ v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4
% 14.58/6.51  
% 14.58/6.51  %Foreground sorts:
% 14.58/6.51  
% 14.58/6.51  
% 14.58/6.51  %Background operators:
% 14.58/6.51  
% 14.58/6.51  
% 14.58/6.51  %Foreground operators:
% 14.58/6.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.58/6.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.58/6.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.58/6.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.58/6.51  tff('#skF_5', type, '#skF_5': $i).
% 14.58/6.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.58/6.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 14.58/6.51  tff('#skF_6', type, '#skF_6': $i).
% 14.58/6.51  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 14.58/6.51  tff('#skF_3', type, '#skF_3': $i).
% 14.58/6.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.58/6.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.58/6.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.58/6.51  tff('#skF_4', type, '#skF_4': $i).
% 14.58/6.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.58/6.51  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 14.58/6.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.58/6.51  
% 14.69/6.54  tff(f_135, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((((B = k1_xboole_0) => (A = k1_xboole_0)) & r1_partfun1(C, D)) & (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r1_partfun1(C, E) & r1_partfun1(D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_2)).
% 14.69/6.54  tff(f_106, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((((B = k1_xboole_0) => (A = k1_xboole_0)) & r1_partfun1(C, D)) & (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((v1_partfun1(E, A) & r1_partfun1(C, E)) & r1_partfun1(D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_partfun1)).
% 14.69/6.54  tff(f_61, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(((B = k1_xboole_0) => (A = k1_xboole_0)) & (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~r1_partfun1(C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_2)).
% 14.69/6.54  tff(f_42, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 14.69/6.54  tff(f_78, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 14.69/6.54  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 14.69/6.54  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 14.69/6.54  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 14.69/6.54  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 14.69/6.54  tff(c_46, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 14.69/6.54  tff(c_48, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_135])).
% 14.69/6.54  tff(c_57, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_48])).
% 14.69/6.54  tff(c_300, plain, (![B_80, A_81, C_82, D_83]: (k1_xboole_0=B_80 | v1_funct_1('#skF_2'(A_81, B_80, C_82, D_83)) | ~r1_partfun1(C_82, D_83) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))) | ~v1_funct_1(D_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))) | ~v1_funct_1(C_82))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.69/6.54  tff(c_306, plain, (![C_82]: (k1_xboole_0='#skF_4' | v1_funct_1('#skF_2'('#skF_3', '#skF_4', C_82, '#skF_6')) | ~r1_partfun1(C_82, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_82))), inference(resolution, [status(thm)], [c_50, c_300])).
% 14.69/6.54  tff(c_313, plain, (![C_82]: (k1_xboole_0='#skF_4' | v1_funct_1('#skF_2'('#skF_3', '#skF_4', C_82, '#skF_6')) | ~r1_partfun1(C_82, '#skF_6') | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_82))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_306])).
% 14.69/6.54  tff(c_319, plain, (![C_84]: (v1_funct_1('#skF_2'('#skF_3', '#skF_4', C_84, '#skF_6')) | ~r1_partfun1(C_84, '#skF_6') | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_84))), inference(negUnitSimplification, [status(thm)], [c_57, c_313])).
% 14.69/6.54  tff(c_329, plain, (v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~r1_partfun1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_319])).
% 14.69/6.54  tff(c_338, plain, (v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_329])).
% 14.69/6.54  tff(c_394, plain, (![B_95, A_96, C_97, D_98]: (k1_xboole_0=B_95 | v1_partfun1('#skF_2'(A_96, B_95, C_97, D_98), A_96) | ~r1_partfun1(C_97, D_98) | ~m1_subset_1(D_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))) | ~v1_funct_1(D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))) | ~v1_funct_1(C_97))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.69/6.54  tff(c_400, plain, (![C_97]: (k1_xboole_0='#skF_4' | v1_partfun1('#skF_2'('#skF_3', '#skF_4', C_97, '#skF_6'), '#skF_3') | ~r1_partfun1(C_97, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_97))), inference(resolution, [status(thm)], [c_50, c_394])).
% 14.69/6.54  tff(c_407, plain, (![C_97]: (k1_xboole_0='#skF_4' | v1_partfun1('#skF_2'('#skF_3', '#skF_4', C_97, '#skF_6'), '#skF_3') | ~r1_partfun1(C_97, '#skF_6') | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_97))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_400])).
% 14.69/6.54  tff(c_413, plain, (![C_99]: (v1_partfun1('#skF_2'('#skF_3', '#skF_4', C_99, '#skF_6'), '#skF_3') | ~r1_partfun1(C_99, '#skF_6') | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_99))), inference(negUnitSimplification, [status(thm)], [c_57, c_407])).
% 14.69/6.54  tff(c_423, plain, (v1_partfun1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3') | ~r1_partfun1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_413])).
% 14.69/6.54  tff(c_432, plain, (v1_partfun1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_423])).
% 14.69/6.54  tff(c_703, plain, (![B_122, A_123, C_124, D_125]: (k1_xboole_0=B_122 | m1_subset_1('#skF_2'(A_123, B_122, C_124, D_125), k1_zfmisc_1(k2_zfmisc_1(A_123, B_122))) | ~r1_partfun1(C_124, D_125) | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_122))) | ~v1_funct_1(D_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_123, B_122))) | ~v1_funct_1(C_124))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.69/6.54  tff(c_20, plain, (![B_5, A_4, C_6]: (k1_xboole_0=B_5 | v1_funct_1('#skF_1'(A_4, B_5, C_6)) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))) | ~v1_funct_1(C_6))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.69/6.54  tff(c_1027, plain, (![A_158, B_159, C_160, D_161]: (v1_funct_1('#skF_1'(A_158, B_159, '#skF_2'(A_158, B_159, C_160, D_161))) | ~v1_funct_1('#skF_2'(A_158, B_159, C_160, D_161)) | k1_xboole_0=B_159 | ~r1_partfun1(C_160, D_161) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~v1_funct_1(D_161) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~v1_funct_1(C_160))), inference(resolution, [status(thm)], [c_703, c_20])).
% 14.69/6.54  tff(c_1037, plain, (![C_160]: (v1_funct_1('#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', C_160, '#skF_6'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', C_160, '#skF_6')) | k1_xboole_0='#skF_4' | ~r1_partfun1(C_160, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_160))), inference(resolution, [status(thm)], [c_50, c_1027])).
% 14.69/6.54  tff(c_1046, plain, (![C_160]: (v1_funct_1('#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', C_160, '#skF_6'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', C_160, '#skF_6')) | k1_xboole_0='#skF_4' | ~r1_partfun1(C_160, '#skF_6') | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_160))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1037])).
% 14.69/6.54  tff(c_1052, plain, (![C_162]: (v1_funct_1('#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', C_162, '#skF_6'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', C_162, '#skF_6')) | ~r1_partfun1(C_162, '#skF_6') | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_162))), inference(negUnitSimplification, [status(thm)], [c_57, c_1046])).
% 14.69/6.54  tff(c_1066, plain, (v1_funct_1('#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~r1_partfun1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_1052])).
% 14.69/6.54  tff(c_1078, plain, (v1_funct_1('#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_338, c_1066])).
% 14.69/6.54  tff(c_38, plain, (![B_14, A_13, C_15, D_19]: (k1_xboole_0=B_14 | m1_subset_1('#skF_2'(A_13, B_14, C_15, D_19), k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~r1_partfun1(C_15, D_19) | ~m1_subset_1(D_19, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(D_19) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.69/6.54  tff(c_16, plain, (![B_5, A_4, C_6]: (k1_xboole_0=B_5 | v1_funct_2('#skF_1'(A_4, B_5, C_6), A_4, B_5) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))) | ~v1_funct_1(C_6))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.69/6.54  tff(c_1191, plain, (![A_177, B_178, C_179, D_180]: (v1_funct_2('#skF_1'(A_177, B_178, '#skF_2'(A_177, B_178, C_179, D_180)), A_177, B_178) | ~v1_funct_1('#skF_2'(A_177, B_178, C_179, D_180)) | k1_xboole_0=B_178 | ~r1_partfun1(C_179, D_180) | ~m1_subset_1(D_180, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))) | ~v1_funct_1(D_180) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))) | ~v1_funct_1(C_179))), inference(resolution, [status(thm)], [c_703, c_16])).
% 14.69/6.54  tff(c_162, plain, (![B_49, A_50, C_51]: (k1_xboole_0=B_49 | m1_subset_1('#skF_1'(A_50, B_49, C_51), k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))) | ~v1_funct_1(C_51))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.69/6.54  tff(c_4, plain, (![B_2, C_3, A_1]: (k1_xboole_0=B_2 | v1_partfun1(C_3, A_1) | ~v1_funct_2(C_3, A_1, B_2) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.69/6.54  tff(c_191, plain, (![A_50, B_49, C_51]: (v1_partfun1('#skF_1'(A_50, B_49, C_51), A_50) | ~v1_funct_2('#skF_1'(A_50, B_49, C_51), A_50, B_49) | ~v1_funct_1('#skF_1'(A_50, B_49, C_51)) | k1_xboole_0=B_49 | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))) | ~v1_funct_1(C_51))), inference(resolution, [status(thm)], [c_162, c_4])).
% 14.69/6.54  tff(c_1580, plain, (![A_314, B_315, C_316, D_317]: (v1_partfun1('#skF_1'(A_314, B_315, '#skF_2'(A_314, B_315, C_316, D_317)), A_314) | ~v1_funct_1('#skF_1'(A_314, B_315, '#skF_2'(A_314, B_315, C_316, D_317))) | ~m1_subset_1('#skF_2'(A_314, B_315, C_316, D_317), k1_zfmisc_1(k2_zfmisc_1(A_314, B_315))) | ~v1_funct_1('#skF_2'(A_314, B_315, C_316, D_317)) | k1_xboole_0=B_315 | ~r1_partfun1(C_316, D_317) | ~m1_subset_1(D_317, k1_zfmisc_1(k2_zfmisc_1(A_314, B_315))) | ~v1_funct_1(D_317) | ~m1_subset_1(C_316, k1_zfmisc_1(k2_zfmisc_1(A_314, B_315))) | ~v1_funct_1(C_316))), inference(resolution, [status(thm)], [c_1191, c_191])).
% 14.69/6.54  tff(c_1585, plain, (![A_13, B_14, C_15, D_19]: (v1_partfun1('#skF_1'(A_13, B_14, '#skF_2'(A_13, B_14, C_15, D_19)), A_13) | ~v1_funct_1('#skF_1'(A_13, B_14, '#skF_2'(A_13, B_14, C_15, D_19))) | ~v1_funct_1('#skF_2'(A_13, B_14, C_15, D_19)) | k1_xboole_0=B_14 | ~r1_partfun1(C_15, D_19) | ~m1_subset_1(D_19, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(D_19) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(resolution, [status(thm)], [c_38, c_1580])).
% 14.69/6.54  tff(c_12, plain, (![B_5, A_4, C_6]: (k1_xboole_0=B_5 | m1_subset_1('#skF_1'(A_4, B_5, C_6), k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))) | ~v1_funct_1(C_6))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.69/6.54  tff(c_8, plain, (![B_5, C_6, A_4]: (k1_xboole_0=B_5 | r1_partfun1(C_6, '#skF_1'(A_4, B_5, C_6)) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))) | ~v1_funct_1(C_6))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.69/6.54  tff(c_1224, plain, (![A_200, B_201, C_202, D_203]: (r1_partfun1('#skF_2'(A_200, B_201, C_202, D_203), '#skF_1'(A_200, B_201, '#skF_2'(A_200, B_201, C_202, D_203))) | ~v1_funct_1('#skF_2'(A_200, B_201, C_202, D_203)) | k1_xboole_0=B_201 | ~r1_partfun1(C_202, D_203) | ~m1_subset_1(D_203, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))) | ~v1_funct_1(D_203) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))) | ~v1_funct_1(C_202))), inference(resolution, [status(thm)], [c_703, c_8])).
% 14.69/6.54  tff(c_22, plain, (![D_12, C_10, A_8, B_9]: (D_12=C_10 | ~r1_partfun1(C_10, D_12) | ~v1_partfun1(D_12, A_8) | ~v1_partfun1(C_10, A_8) | ~m1_subset_1(D_12, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_1(D_12) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_1(C_10))), inference(cnfTransformation, [status(thm)], [f_78])).
% 14.69/6.54  tff(c_3693, plain, (![C_487, D_490, A_491, B_486, B_489, A_488]: ('#skF_1'(A_491, B_486, '#skF_2'(A_491, B_486, C_487, D_490))='#skF_2'(A_491, B_486, C_487, D_490) | ~v1_partfun1('#skF_1'(A_491, B_486, '#skF_2'(A_491, B_486, C_487, D_490)), A_488) | ~v1_partfun1('#skF_2'(A_491, B_486, C_487, D_490), A_488) | ~m1_subset_1('#skF_1'(A_491, B_486, '#skF_2'(A_491, B_486, C_487, D_490)), k1_zfmisc_1(k2_zfmisc_1(A_488, B_489))) | ~v1_funct_1('#skF_1'(A_491, B_486, '#skF_2'(A_491, B_486, C_487, D_490))) | ~m1_subset_1('#skF_2'(A_491, B_486, C_487, D_490), k1_zfmisc_1(k2_zfmisc_1(A_488, B_489))) | ~v1_funct_1('#skF_2'(A_491, B_486, C_487, D_490)) | k1_xboole_0=B_486 | ~r1_partfun1(C_487, D_490) | ~m1_subset_1(D_490, k1_zfmisc_1(k2_zfmisc_1(A_491, B_486))) | ~v1_funct_1(D_490) | ~m1_subset_1(C_487, k1_zfmisc_1(k2_zfmisc_1(A_491, B_486))) | ~v1_funct_1(C_487))), inference(resolution, [status(thm)], [c_1224, c_22])).
% 14.69/6.54  tff(c_9381, plain, (![A_710, B_711, C_712, D_713]: ('#skF_1'(A_710, B_711, '#skF_2'(A_710, B_711, C_712, D_713))='#skF_2'(A_710, B_711, C_712, D_713) | ~v1_partfun1('#skF_1'(A_710, B_711, '#skF_2'(A_710, B_711, C_712, D_713)), A_710) | ~v1_partfun1('#skF_2'(A_710, B_711, C_712, D_713), A_710) | ~v1_funct_1('#skF_1'(A_710, B_711, '#skF_2'(A_710, B_711, C_712, D_713))) | ~r1_partfun1(C_712, D_713) | ~m1_subset_1(D_713, k1_zfmisc_1(k2_zfmisc_1(A_710, B_711))) | ~v1_funct_1(D_713) | ~m1_subset_1(C_712, k1_zfmisc_1(k2_zfmisc_1(A_710, B_711))) | ~v1_funct_1(C_712) | k1_xboole_0=B_711 | ~m1_subset_1('#skF_2'(A_710, B_711, C_712, D_713), k1_zfmisc_1(k2_zfmisc_1(A_710, B_711))) | ~v1_funct_1('#skF_2'(A_710, B_711, C_712, D_713)))), inference(resolution, [status(thm)], [c_12, c_3693])).
% 14.69/6.54  tff(c_9453, plain, (![A_715, B_716, C_717, D_718]: ('#skF_1'(A_715, B_716, '#skF_2'(A_715, B_716, C_717, D_718))='#skF_2'(A_715, B_716, C_717, D_718) | ~v1_partfun1('#skF_2'(A_715, B_716, C_717, D_718), A_715) | ~m1_subset_1('#skF_2'(A_715, B_716, C_717, D_718), k1_zfmisc_1(k2_zfmisc_1(A_715, B_716))) | ~v1_funct_1('#skF_1'(A_715, B_716, '#skF_2'(A_715, B_716, C_717, D_718))) | ~v1_funct_1('#skF_2'(A_715, B_716, C_717, D_718)) | k1_xboole_0=B_716 | ~r1_partfun1(C_717, D_718) | ~m1_subset_1(D_718, k1_zfmisc_1(k2_zfmisc_1(A_715, B_716))) | ~v1_funct_1(D_718) | ~m1_subset_1(C_717, k1_zfmisc_1(k2_zfmisc_1(A_715, B_716))) | ~v1_funct_1(C_717))), inference(resolution, [status(thm)], [c_1585, c_9381])).
% 14.69/6.54  tff(c_9492, plain, (![A_719, B_720, C_721, D_722]: ('#skF_1'(A_719, B_720, '#skF_2'(A_719, B_720, C_721, D_722))='#skF_2'(A_719, B_720, C_721, D_722) | ~v1_partfun1('#skF_2'(A_719, B_720, C_721, D_722), A_719) | ~v1_funct_1('#skF_1'(A_719, B_720, '#skF_2'(A_719, B_720, C_721, D_722))) | ~v1_funct_1('#skF_2'(A_719, B_720, C_721, D_722)) | k1_xboole_0=B_720 | ~r1_partfun1(C_721, D_722) | ~m1_subset_1(D_722, k1_zfmisc_1(k2_zfmisc_1(A_719, B_720))) | ~v1_funct_1(D_722) | ~m1_subset_1(C_721, k1_zfmisc_1(k2_zfmisc_1(A_719, B_720))) | ~v1_funct_1(C_721))), inference(resolution, [status(thm)], [c_38, c_9453])).
% 14.69/6.54  tff(c_9526, plain, ('#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~v1_partfun1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3') | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_4' | ~r1_partfun1('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_1078, c_9492])).
% 14.69/6.54  tff(c_9569, plain, ('#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_46, c_338, c_432, c_9526])).
% 14.69/6.54  tff(c_9570, plain, ('#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_57, c_9569])).
% 14.69/6.54  tff(c_561, plain, (![B_109, C_110, A_111, D_112]: (k1_xboole_0=B_109 | r1_partfun1(C_110, '#skF_2'(A_111, B_109, C_110, D_112)) | ~r1_partfun1(C_110, D_112) | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_111, B_109))) | ~v1_funct_1(D_112) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_109))) | ~v1_funct_1(C_110))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.69/6.54  tff(c_567, plain, (![C_110]: (k1_xboole_0='#skF_4' | r1_partfun1(C_110, '#skF_2'('#skF_3', '#skF_4', C_110, '#skF_6')) | ~r1_partfun1(C_110, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_110))), inference(resolution, [status(thm)], [c_50, c_561])).
% 14.69/6.54  tff(c_574, plain, (![C_110]: (k1_xboole_0='#skF_4' | r1_partfun1(C_110, '#skF_2'('#skF_3', '#skF_4', C_110, '#skF_6')) | ~r1_partfun1(C_110, '#skF_6') | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_110))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_567])).
% 14.69/6.54  tff(c_639, plain, (![C_116]: (r1_partfun1(C_116, '#skF_2'('#skF_3', '#skF_4', C_116, '#skF_6')) | ~r1_partfun1(C_116, '#skF_6') | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_116))), inference(negUnitSimplification, [status(thm)], [c_57, c_574])).
% 14.69/6.54  tff(c_646, plain, (r1_partfun1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~r1_partfun1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_639])).
% 14.69/6.54  tff(c_655, plain, (r1_partfun1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_646])).
% 14.69/6.54  tff(c_475, plain, (![B_102, D_103, A_104, C_105]: (k1_xboole_0=B_102 | r1_partfun1(D_103, '#skF_2'(A_104, B_102, C_105, D_103)) | ~r1_partfun1(C_105, D_103) | ~m1_subset_1(D_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))) | ~v1_funct_1(D_103) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))) | ~v1_funct_1(C_105))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.69/6.54  tff(c_481, plain, (![C_105]: (k1_xboole_0='#skF_4' | r1_partfun1('#skF_6', '#skF_2'('#skF_3', '#skF_4', C_105, '#skF_6')) | ~r1_partfun1(C_105, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_105))), inference(resolution, [status(thm)], [c_50, c_475])).
% 14.69/6.54  tff(c_488, plain, (![C_105]: (k1_xboole_0='#skF_4' | r1_partfun1('#skF_6', '#skF_2'('#skF_3', '#skF_4', C_105, '#skF_6')) | ~r1_partfun1(C_105, '#skF_6') | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_105))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_481])).
% 14.69/6.54  tff(c_494, plain, (![C_106]: (r1_partfun1('#skF_6', '#skF_2'('#skF_3', '#skF_4', C_106, '#skF_6')) | ~r1_partfun1(C_106, '#skF_6') | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_106))), inference(negUnitSimplification, [status(thm)], [c_57, c_488])).
% 14.69/6.54  tff(c_504, plain, (r1_partfun1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~r1_partfun1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_494])).
% 14.69/6.54  tff(c_513, plain, (r1_partfun1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_504])).
% 14.69/6.54  tff(c_843, plain, (![A_123, B_122, C_124, D_125]: (v1_funct_2('#skF_1'(A_123, B_122, '#skF_2'(A_123, B_122, C_124, D_125)), A_123, B_122) | ~v1_funct_1('#skF_2'(A_123, B_122, C_124, D_125)) | k1_xboole_0=B_122 | ~r1_partfun1(C_124, D_125) | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_122))) | ~v1_funct_1(D_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_123, B_122))) | ~v1_funct_1(C_124))), inference(resolution, [status(thm)], [c_703, c_16])).
% 14.69/6.54  tff(c_44, plain, (![E_25]: (~r1_partfun1('#skF_6', E_25) | ~r1_partfun1('#skF_5', E_25) | ~m1_subset_1(E_25, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2(E_25, '#skF_3', '#skF_4') | ~v1_funct_1(E_25))), inference(cnfTransformation, [status(thm)], [f_135])).
% 14.69/6.54  tff(c_183, plain, (![C_51]: (~r1_partfun1('#skF_6', '#skF_1'('#skF_3', '#skF_4', C_51)) | ~r1_partfun1('#skF_5', '#skF_1'('#skF_3', '#skF_4', C_51)) | ~v1_funct_2('#skF_1'('#skF_3', '#skF_4', C_51), '#skF_3', '#skF_4') | ~v1_funct_1('#skF_1'('#skF_3', '#skF_4', C_51)) | k1_xboole_0='#skF_4' | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_51))), inference(resolution, [status(thm)], [c_162, c_44])).
% 14.69/6.54  tff(c_199, plain, (![C_51]: (~r1_partfun1('#skF_6', '#skF_1'('#skF_3', '#skF_4', C_51)) | ~r1_partfun1('#skF_5', '#skF_1'('#skF_3', '#skF_4', C_51)) | ~v1_funct_2('#skF_1'('#skF_3', '#skF_4', C_51), '#skF_3', '#skF_4') | ~v1_funct_1('#skF_1'('#skF_3', '#skF_4', C_51)) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_51))), inference(negUnitSimplification, [status(thm)], [c_57, c_183])).
% 14.69/6.54  tff(c_767, plain, (![C_124, D_125]: (~r1_partfun1('#skF_6', '#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', C_124, D_125))) | ~r1_partfun1('#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', C_124, D_125))) | ~v1_funct_2('#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', C_124, D_125)), '#skF_3', '#skF_4') | ~v1_funct_1('#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', C_124, D_125))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', C_124, D_125)) | k1_xboole_0='#skF_4' | ~r1_partfun1(C_124, D_125) | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(D_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_124))), inference(resolution, [status(thm)], [c_703, c_199])).
% 14.69/6.54  tff(c_1604, plain, (![C_361, D_362]: (~r1_partfun1('#skF_6', '#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', C_361, D_362))) | ~r1_partfun1('#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', C_361, D_362))) | ~v1_funct_2('#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', C_361, D_362)), '#skF_3', '#skF_4') | ~v1_funct_1('#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', C_361, D_362))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', C_361, D_362)) | ~r1_partfun1(C_361, D_362) | ~m1_subset_1(D_362, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(D_362) | ~m1_subset_1(C_361, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_361))), inference(negUnitSimplification, [status(thm)], [c_57, c_767])).
% 14.69/6.54  tff(c_1608, plain, (![C_124, D_125]: (~r1_partfun1('#skF_6', '#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', C_124, D_125))) | ~r1_partfun1('#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', C_124, D_125))) | ~v1_funct_1('#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', C_124, D_125))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', C_124, D_125)) | k1_xboole_0='#skF_4' | ~r1_partfun1(C_124, D_125) | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(D_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_124))), inference(resolution, [status(thm)], [c_843, c_1604])).
% 14.69/6.54  tff(c_1611, plain, (![C_124, D_125]: (~r1_partfun1('#skF_6', '#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', C_124, D_125))) | ~r1_partfun1('#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', C_124, D_125))) | ~v1_funct_1('#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', C_124, D_125))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', C_124, D_125)) | ~r1_partfun1(C_124, D_125) | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(D_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1(C_124))), inference(negUnitSimplification, [status(thm)], [c_57, c_1608])).
% 14.69/6.54  tff(c_9652, plain, (~r1_partfun1('#skF_6', '#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~r1_partfun1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_1('#skF_1'('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~r1_partfun1('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9570, c_1611])).
% 14.69/6.54  tff(c_9874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_46, c_338, c_338, c_9570, c_655, c_513, c_9570, c_9652])).
% 14.69/6.54  tff(c_9876, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_48])).
% 14.69/6.54  tff(c_9875, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_48])).
% 14.69/6.54  tff(c_9881, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9876, c_9875])).
% 14.69/6.54  tff(c_9890, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9881, c_54])).
% 14.69/6.54  tff(c_9891, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9881, c_50])).
% 14.69/6.54  tff(c_40, plain, (![B_14, C_15, D_19]: (v1_funct_1('#skF_2'(k1_xboole_0, B_14, C_15, D_19)) | ~r1_partfun1(C_15, D_19) | ~m1_subset_1(D_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))) | ~v1_funct_1(D_19) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.69/6.54  tff(c_10156, plain, (![B_757, C_758, D_759]: (v1_funct_1('#skF_2'('#skF_4', B_757, C_758, D_759)) | ~r1_partfun1(C_758, D_759) | ~m1_subset_1(D_759, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_757))) | ~v1_funct_1(D_759) | ~m1_subset_1(C_758, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_757))) | ~v1_funct_1(C_758))), inference(demodulation, [status(thm), theory('equality')], [c_9876, c_9876, c_9876, c_40])).
% 14.69/6.54  tff(c_10163, plain, (![C_758]: (v1_funct_1('#skF_2'('#skF_4', '#skF_4', C_758, '#skF_6')) | ~r1_partfun1(C_758, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_758, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1(C_758))), inference(resolution, [status(thm)], [c_9891, c_10156])).
% 14.69/6.54  tff(c_10174, plain, (![C_760]: (v1_funct_1('#skF_2'('#skF_4', '#skF_4', C_760, '#skF_6')) | ~r1_partfun1(C_760, '#skF_6') | ~m1_subset_1(C_760, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1(C_760))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_10163])).
% 14.69/6.54  tff(c_10188, plain, (v1_funct_1('#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6')) | ~r1_partfun1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_9890, c_10174])).
% 14.69/6.54  tff(c_10197, plain, (v1_funct_1('#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_10188])).
% 14.69/6.54  tff(c_32, plain, (![B_14, C_15, D_19]: (v1_partfun1('#skF_2'(k1_xboole_0, B_14, C_15, D_19), k1_xboole_0) | ~r1_partfun1(C_15, D_19) | ~m1_subset_1(D_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))) | ~v1_funct_1(D_19) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.69/6.54  tff(c_10392, plain, (![B_779, C_780, D_781]: (v1_partfun1('#skF_2'('#skF_4', B_779, C_780, D_781), '#skF_4') | ~r1_partfun1(C_780, D_781) | ~m1_subset_1(D_781, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_779))) | ~v1_funct_1(D_781) | ~m1_subset_1(C_780, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_779))) | ~v1_funct_1(C_780))), inference(demodulation, [status(thm), theory('equality')], [c_9876, c_9876, c_9876, c_9876, c_32])).
% 14.69/6.54  tff(c_10399, plain, (![C_780]: (v1_partfun1('#skF_2'('#skF_4', '#skF_4', C_780, '#skF_6'), '#skF_4') | ~r1_partfun1(C_780, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_780, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1(C_780))), inference(resolution, [status(thm)], [c_9891, c_10392])).
% 14.69/6.54  tff(c_10410, plain, (![C_782]: (v1_partfun1('#skF_2'('#skF_4', '#skF_4', C_782, '#skF_6'), '#skF_4') | ~r1_partfun1(C_782, '#skF_6') | ~m1_subset_1(C_782, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1(C_782))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_10399])).
% 14.69/6.54  tff(c_10424, plain, (v1_partfun1('#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6'), '#skF_4') | ~r1_partfun1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_9890, c_10410])).
% 14.69/6.54  tff(c_10433, plain, (v1_partfun1('#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_10424])).
% 14.69/6.54  tff(c_36, plain, (![B_14, C_15, D_19]: (m1_subset_1('#skF_2'(k1_xboole_0, B_14, C_15, D_19), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))) | ~r1_partfun1(C_15, D_19) | ~m1_subset_1(D_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))) | ~v1_funct_1(D_19) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.69/6.54  tff(c_10642, plain, (![B_816, C_817, D_818]: (m1_subset_1('#skF_2'('#skF_4', B_816, C_817, D_818), k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_816))) | ~r1_partfun1(C_817, D_818) | ~m1_subset_1(D_818, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_816))) | ~v1_funct_1(D_818) | ~m1_subset_1(C_817, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_816))) | ~v1_funct_1(C_817))), inference(demodulation, [status(thm), theory('equality')], [c_9876, c_9876, c_9876, c_9876, c_36])).
% 14.69/6.54  tff(c_18, plain, (![B_5, C_6]: (v1_funct_1('#skF_1'(k1_xboole_0, B_5, C_6)) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_5))) | ~v1_funct_1(C_6))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.69/6.54  tff(c_9892, plain, (![B_5, C_6]: (v1_funct_1('#skF_1'('#skF_4', B_5, C_6)) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_5))) | ~v1_funct_1(C_6))), inference(demodulation, [status(thm), theory('equality')], [c_9876, c_9876, c_18])).
% 14.69/6.54  tff(c_10941, plain, (![B_834, C_835, D_836]: (v1_funct_1('#skF_1'('#skF_4', B_834, '#skF_2'('#skF_4', B_834, C_835, D_836))) | ~v1_funct_1('#skF_2'('#skF_4', B_834, C_835, D_836)) | ~r1_partfun1(C_835, D_836) | ~m1_subset_1(D_836, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_834))) | ~v1_funct_1(D_836) | ~m1_subset_1(C_835, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_834))) | ~v1_funct_1(C_835))), inference(resolution, [status(thm)], [c_10642, c_9892])).
% 14.69/6.54  tff(c_10953, plain, (![C_835]: (v1_funct_1('#skF_1'('#skF_4', '#skF_4', '#skF_2'('#skF_4', '#skF_4', C_835, '#skF_6'))) | ~v1_funct_1('#skF_2'('#skF_4', '#skF_4', C_835, '#skF_6')) | ~r1_partfun1(C_835, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_835, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1(C_835))), inference(resolution, [status(thm)], [c_9891, c_10941])).
% 14.69/6.54  tff(c_10966, plain, (![C_837]: (v1_funct_1('#skF_1'('#skF_4', '#skF_4', '#skF_2'('#skF_4', '#skF_4', C_837, '#skF_6'))) | ~v1_funct_1('#skF_2'('#skF_4', '#skF_4', C_837, '#skF_6')) | ~r1_partfun1(C_837, '#skF_6') | ~m1_subset_1(C_837, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1(C_837))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_10953])).
% 14.69/6.54  tff(c_10988, plain, (v1_funct_1('#skF_1'('#skF_4', '#skF_4', '#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6')) | ~r1_partfun1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_9890, c_10966])).
% 14.69/6.54  tff(c_11000, plain, (v1_funct_1('#skF_1'('#skF_4', '#skF_4', '#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_10197, c_10988])).
% 14.69/6.54  tff(c_10641, plain, (![B_14, C_15, D_19]: (m1_subset_1('#skF_2'('#skF_4', B_14, C_15, D_19), k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_14))) | ~r1_partfun1(C_15, D_19) | ~m1_subset_1(D_19, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_14))) | ~v1_funct_1(D_19) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_14))) | ~v1_funct_1(C_15))), inference(demodulation, [status(thm), theory('equality')], [c_9876, c_9876, c_9876, c_9876, c_36])).
% 14.69/6.54  tff(c_14, plain, (![B_5, C_6]: (v1_funct_2('#skF_1'(k1_xboole_0, B_5, C_6), k1_xboole_0, B_5) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_5))) | ~v1_funct_1(C_6))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.69/6.54  tff(c_9948, plain, (![B_5, C_6]: (v1_funct_2('#skF_1'('#skF_4', B_5, C_6), '#skF_4', B_5) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_5))) | ~v1_funct_1(C_6))), inference(demodulation, [status(thm), theory('equality')], [c_9876, c_9876, c_9876, c_14])).
% 14.69/6.54  tff(c_11196, plain, (![B_859, C_860, D_861]: (v1_funct_2('#skF_1'('#skF_4', B_859, '#skF_2'('#skF_4', B_859, C_860, D_861)), '#skF_4', B_859) | ~v1_funct_1('#skF_2'('#skF_4', B_859, C_860, D_861)) | ~r1_partfun1(C_860, D_861) | ~m1_subset_1(D_861, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_859))) | ~v1_funct_1(D_861) | ~m1_subset_1(C_860, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_859))) | ~v1_funct_1(C_860))), inference(resolution, [status(thm)], [c_10642, c_9948])).
% 14.69/6.54  tff(c_10, plain, (![B_5, C_6]: (m1_subset_1('#skF_1'(k1_xboole_0, B_5, C_6), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_5))) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_5))) | ~v1_funct_1(C_6))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.69/6.54  tff(c_10005, plain, (![B_741, C_742]: (m1_subset_1('#skF_1'('#skF_4', B_741, C_742), k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_741))) | ~m1_subset_1(C_742, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_741))) | ~v1_funct_1(C_742))), inference(demodulation, [status(thm), theory('equality')], [c_9876, c_9876, c_9876, c_10])).
% 14.69/6.54  tff(c_2, plain, (![C_3, B_2]: (v1_partfun1(C_3, k1_xboole_0) | ~v1_funct_2(C_3, k1_xboole_0, B_2) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.69/6.54  tff(c_9934, plain, (![C_3, B_2]: (v1_partfun1(C_3, '#skF_4') | ~v1_funct_2(C_3, '#skF_4', B_2) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_2))) | ~v1_funct_1(C_3))), inference(demodulation, [status(thm), theory('equality')], [c_9876, c_9876, c_9876, c_2])).
% 14.69/6.54  tff(c_10031, plain, (![B_741, C_742]: (v1_partfun1('#skF_1'('#skF_4', B_741, C_742), '#skF_4') | ~v1_funct_2('#skF_1'('#skF_4', B_741, C_742), '#skF_4', B_741) | ~v1_funct_1('#skF_1'('#skF_4', B_741, C_742)) | ~m1_subset_1(C_742, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_741))) | ~v1_funct_1(C_742))), inference(resolution, [status(thm)], [c_10005, c_9934])).
% 14.69/6.54  tff(c_11790, plain, (![B_1001, C_1002, D_1003]: (v1_partfun1('#skF_1'('#skF_4', B_1001, '#skF_2'('#skF_4', B_1001, C_1002, D_1003)), '#skF_4') | ~v1_funct_1('#skF_1'('#skF_4', B_1001, '#skF_2'('#skF_4', B_1001, C_1002, D_1003))) | ~m1_subset_1('#skF_2'('#skF_4', B_1001, C_1002, D_1003), k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_1001))) | ~v1_funct_1('#skF_2'('#skF_4', B_1001, C_1002, D_1003)) | ~r1_partfun1(C_1002, D_1003) | ~m1_subset_1(D_1003, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_1001))) | ~v1_funct_1(D_1003) | ~m1_subset_1(C_1002, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_1001))) | ~v1_funct_1(C_1002))), inference(resolution, [status(thm)], [c_11196, c_10031])).
% 14.69/6.54  tff(c_11799, plain, (![B_14, C_15, D_19]: (v1_partfun1('#skF_1'('#skF_4', B_14, '#skF_2'('#skF_4', B_14, C_15, D_19)), '#skF_4') | ~v1_funct_1('#skF_1'('#skF_4', B_14, '#skF_2'('#skF_4', B_14, C_15, D_19))) | ~v1_funct_1('#skF_2'('#skF_4', B_14, C_15, D_19)) | ~r1_partfun1(C_15, D_19) | ~m1_subset_1(D_19, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_14))) | ~v1_funct_1(D_19) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_14))) | ~v1_funct_1(C_15))), inference(resolution, [status(thm)], [c_10641, c_11790])).
% 14.69/6.54  tff(c_10004, plain, (![B_5, C_6]: (m1_subset_1('#skF_1'('#skF_4', B_5, C_6), k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_5))) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_5))) | ~v1_funct_1(C_6))), inference(demodulation, [status(thm), theory('equality')], [c_9876, c_9876, c_9876, c_10])).
% 14.69/6.54  tff(c_6, plain, (![C_6, B_5]: (r1_partfun1(C_6, '#skF_1'(k1_xboole_0, B_5, C_6)) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_5))) | ~v1_funct_1(C_6))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.69/6.54  tff(c_9906, plain, (![C_6, B_5]: (r1_partfun1(C_6, '#skF_1'('#skF_4', B_5, C_6)) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_5))) | ~v1_funct_1(C_6))), inference(demodulation, [status(thm), theory('equality')], [c_9876, c_9876, c_6])).
% 14.69/6.54  tff(c_11251, plain, (![B_877, C_878, D_879]: (r1_partfun1('#skF_2'('#skF_4', B_877, C_878, D_879), '#skF_1'('#skF_4', B_877, '#skF_2'('#skF_4', B_877, C_878, D_879))) | ~v1_funct_1('#skF_2'('#skF_4', B_877, C_878, D_879)) | ~r1_partfun1(C_878, D_879) | ~m1_subset_1(D_879, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_877))) | ~v1_funct_1(D_879) | ~m1_subset_1(C_878, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_877))) | ~v1_funct_1(C_878))), inference(resolution, [status(thm)], [c_10642, c_9906])).
% 14.69/6.54  tff(c_13677, plain, (![D_1169, B_1167, C_1165, B_1168, A_1166]: ('#skF_1'('#skF_4', B_1168, '#skF_2'('#skF_4', B_1168, C_1165, D_1169))='#skF_2'('#skF_4', B_1168, C_1165, D_1169) | ~v1_partfun1('#skF_1'('#skF_4', B_1168, '#skF_2'('#skF_4', B_1168, C_1165, D_1169)), A_1166) | ~v1_partfun1('#skF_2'('#skF_4', B_1168, C_1165, D_1169), A_1166) | ~m1_subset_1('#skF_1'('#skF_4', B_1168, '#skF_2'('#skF_4', B_1168, C_1165, D_1169)), k1_zfmisc_1(k2_zfmisc_1(A_1166, B_1167))) | ~v1_funct_1('#skF_1'('#skF_4', B_1168, '#skF_2'('#skF_4', B_1168, C_1165, D_1169))) | ~m1_subset_1('#skF_2'('#skF_4', B_1168, C_1165, D_1169), k1_zfmisc_1(k2_zfmisc_1(A_1166, B_1167))) | ~v1_funct_1('#skF_2'('#skF_4', B_1168, C_1165, D_1169)) | ~r1_partfun1(C_1165, D_1169) | ~m1_subset_1(D_1169, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_1168))) | ~v1_funct_1(D_1169) | ~m1_subset_1(C_1165, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_1168))) | ~v1_funct_1(C_1165))), inference(resolution, [status(thm)], [c_11251, c_22])).
% 14.69/6.54  tff(c_18697, plain, (![B_1313, C_1314, D_1315]: ('#skF_1'('#skF_4', B_1313, '#skF_2'('#skF_4', B_1313, C_1314, D_1315))='#skF_2'('#skF_4', B_1313, C_1314, D_1315) | ~v1_partfun1('#skF_1'('#skF_4', B_1313, '#skF_2'('#skF_4', B_1313, C_1314, D_1315)), '#skF_4') | ~v1_partfun1('#skF_2'('#skF_4', B_1313, C_1314, D_1315), '#skF_4') | ~v1_funct_1('#skF_1'('#skF_4', B_1313, '#skF_2'('#skF_4', B_1313, C_1314, D_1315))) | ~r1_partfun1(C_1314, D_1315) | ~m1_subset_1(D_1315, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_1313))) | ~v1_funct_1(D_1315) | ~m1_subset_1(C_1314, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_1313))) | ~v1_funct_1(C_1314) | ~m1_subset_1('#skF_2'('#skF_4', B_1313, C_1314, D_1315), k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_1313))) | ~v1_funct_1('#skF_2'('#skF_4', B_1313, C_1314, D_1315)))), inference(resolution, [status(thm)], [c_10004, c_13677])).
% 14.69/6.54  tff(c_19427, plain, (![B_1341, C_1342, D_1343]: ('#skF_1'('#skF_4', B_1341, '#skF_2'('#skF_4', B_1341, C_1342, D_1343))='#skF_2'('#skF_4', B_1341, C_1342, D_1343) | ~v1_partfun1('#skF_1'('#skF_4', B_1341, '#skF_2'('#skF_4', B_1341, C_1342, D_1343)), '#skF_4') | ~v1_partfun1('#skF_2'('#skF_4', B_1341, C_1342, D_1343), '#skF_4') | ~v1_funct_1('#skF_1'('#skF_4', B_1341, '#skF_2'('#skF_4', B_1341, C_1342, D_1343))) | ~v1_funct_1('#skF_2'('#skF_4', B_1341, C_1342, D_1343)) | ~r1_partfun1(C_1342, D_1343) | ~m1_subset_1(D_1343, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_1341))) | ~v1_funct_1(D_1343) | ~m1_subset_1(C_1342, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_1341))) | ~v1_funct_1(C_1342))), inference(resolution, [status(thm)], [c_10641, c_18697])).
% 14.69/6.54  tff(c_19457, plain, (![B_1344, C_1345, D_1346]: ('#skF_1'('#skF_4', B_1344, '#skF_2'('#skF_4', B_1344, C_1345, D_1346))='#skF_2'('#skF_4', B_1344, C_1345, D_1346) | ~v1_partfun1('#skF_2'('#skF_4', B_1344, C_1345, D_1346), '#skF_4') | ~v1_funct_1('#skF_1'('#skF_4', B_1344, '#skF_2'('#skF_4', B_1344, C_1345, D_1346))) | ~v1_funct_1('#skF_2'('#skF_4', B_1344, C_1345, D_1346)) | ~r1_partfun1(C_1345, D_1346) | ~m1_subset_1(D_1346, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_1344))) | ~v1_funct_1(D_1346) | ~m1_subset_1(C_1345, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_1344))) | ~v1_funct_1(C_1345))), inference(resolution, [status(thm)], [c_11799, c_19427])).
% 14.69/6.54  tff(c_19489, plain, ('#skF_1'('#skF_4', '#skF_4', '#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6'))='#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6') | ~v1_partfun1('#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6'), '#skF_4') | ~v1_funct_1('#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6')) | ~r1_partfun1('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_11000, c_19457])).
% 14.69/6.54  tff(c_19522, plain, ('#skF_1'('#skF_4', '#skF_4', '#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6'))='#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_9890, c_52, c_9891, c_46, c_10197, c_10433, c_19489])).
% 14.69/6.54  tff(c_28, plain, (![C_15, B_14, D_19]: (r1_partfun1(C_15, '#skF_2'(k1_xboole_0, B_14, C_15, D_19)) | ~r1_partfun1(C_15, D_19) | ~m1_subset_1(D_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))) | ~v1_funct_1(D_19) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.69/6.54  tff(c_10226, plain, (![C_762, B_763, D_764]: (r1_partfun1(C_762, '#skF_2'('#skF_4', B_763, C_762, D_764)) | ~r1_partfun1(C_762, D_764) | ~m1_subset_1(D_764, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_763))) | ~v1_funct_1(D_764) | ~m1_subset_1(C_762, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_763))) | ~v1_funct_1(C_762))), inference(demodulation, [status(thm), theory('equality')], [c_9876, c_9876, c_9876, c_28])).
% 14.69/6.54  tff(c_10233, plain, (![C_762]: (r1_partfun1(C_762, '#skF_2'('#skF_4', '#skF_4', C_762, '#skF_6')) | ~r1_partfun1(C_762, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_762, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1(C_762))), inference(resolution, [status(thm)], [c_9891, c_10226])).
% 14.69/6.54  tff(c_10244, plain, (![C_765]: (r1_partfun1(C_765, '#skF_2'('#skF_4', '#skF_4', C_765, '#skF_6')) | ~r1_partfun1(C_765, '#skF_6') | ~m1_subset_1(C_765, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1(C_765))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_10233])).
% 14.69/6.54  tff(c_10254, plain, (r1_partfun1('#skF_5', '#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6')) | ~r1_partfun1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_9890, c_10244])).
% 14.69/6.54  tff(c_10263, plain, (r1_partfun1('#skF_5', '#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_10254])).
% 14.69/6.54  tff(c_24, plain, (![D_19, B_14, C_15]: (r1_partfun1(D_19, '#skF_2'(k1_xboole_0, B_14, C_15, D_19)) | ~r1_partfun1(C_15, D_19) | ~m1_subset_1(D_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))) | ~v1_funct_1(D_19) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.69/6.54  tff(c_10292, plain, (![D_770, B_771, C_772]: (r1_partfun1(D_770, '#skF_2'('#skF_4', B_771, C_772, D_770)) | ~r1_partfun1(C_772, D_770) | ~m1_subset_1(D_770, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_771))) | ~v1_funct_1(D_770) | ~m1_subset_1(C_772, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_771))) | ~v1_funct_1(C_772))), inference(demodulation, [status(thm), theory('equality')], [c_9876, c_9876, c_9876, c_24])).
% 14.69/6.54  tff(c_10299, plain, (![C_772]: (r1_partfun1('#skF_6', '#skF_2'('#skF_4', '#skF_4', C_772, '#skF_6')) | ~r1_partfun1(C_772, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_772, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1(C_772))), inference(resolution, [status(thm)], [c_9891, c_10292])).
% 14.69/6.54  tff(c_10310, plain, (![C_773]: (r1_partfun1('#skF_6', '#skF_2'('#skF_4', '#skF_4', C_773, '#skF_6')) | ~r1_partfun1(C_773, '#skF_6') | ~m1_subset_1(C_773, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1(C_773))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_10299])).
% 14.69/6.54  tff(c_10324, plain, (r1_partfun1('#skF_6', '#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6')) | ~r1_partfun1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_9890, c_10310])).
% 14.69/6.54  tff(c_10333, plain, (r1_partfun1('#skF_6', '#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_10324])).
% 14.69/6.54  tff(c_9918, plain, (![E_25]: (~r1_partfun1('#skF_6', E_25) | ~r1_partfun1('#skF_5', E_25) | ~m1_subset_1(E_25, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_2(E_25, '#skF_4', '#skF_4') | ~v1_funct_1(E_25))), inference(demodulation, [status(thm), theory('equality')], [c_9881, c_9881, c_44])).
% 14.69/6.54  tff(c_10032, plain, (![C_742]: (~r1_partfun1('#skF_6', '#skF_1'('#skF_4', '#skF_4', C_742)) | ~r1_partfun1('#skF_5', '#skF_1'('#skF_4', '#skF_4', C_742)) | ~v1_funct_2('#skF_1'('#skF_4', '#skF_4', C_742), '#skF_4', '#skF_4') | ~v1_funct_1('#skF_1'('#skF_4', '#skF_4', C_742)) | ~m1_subset_1(C_742, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1(C_742))), inference(resolution, [status(thm)], [c_10005, c_9918])).
% 14.69/6.54  tff(c_10748, plain, (![C_817, D_818]: (~r1_partfun1('#skF_6', '#skF_1'('#skF_4', '#skF_4', '#skF_2'('#skF_4', '#skF_4', C_817, D_818))) | ~r1_partfun1('#skF_5', '#skF_1'('#skF_4', '#skF_4', '#skF_2'('#skF_4', '#skF_4', C_817, D_818))) | ~v1_funct_2('#skF_1'('#skF_4', '#skF_4', '#skF_2'('#skF_4', '#skF_4', C_817, D_818)), '#skF_4', '#skF_4') | ~v1_funct_1('#skF_1'('#skF_4', '#skF_4', '#skF_2'('#skF_4', '#skF_4', C_817, D_818))) | ~v1_funct_1('#skF_2'('#skF_4', '#skF_4', C_817, D_818)) | ~r1_partfun1(C_817, D_818) | ~m1_subset_1(D_818, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1(D_818) | ~m1_subset_1(C_817, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1(C_817))), inference(resolution, [status(thm)], [c_10642, c_10032])).
% 14.69/6.54  tff(c_11205, plain, (![C_860, D_861]: (~r1_partfun1('#skF_6', '#skF_1'('#skF_4', '#skF_4', '#skF_2'('#skF_4', '#skF_4', C_860, D_861))) | ~r1_partfun1('#skF_5', '#skF_1'('#skF_4', '#skF_4', '#skF_2'('#skF_4', '#skF_4', C_860, D_861))) | ~v1_funct_1('#skF_1'('#skF_4', '#skF_4', '#skF_2'('#skF_4', '#skF_4', C_860, D_861))) | ~v1_funct_1('#skF_2'('#skF_4', '#skF_4', C_860, D_861)) | ~r1_partfun1(C_860, D_861) | ~m1_subset_1(D_861, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1(D_861) | ~m1_subset_1(C_860, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1(C_860))), inference(resolution, [status(thm)], [c_11196, c_10748])).
% 14.69/6.54  tff(c_19690, plain, (~r1_partfun1('#skF_6', '#skF_1'('#skF_4', '#skF_4', '#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6'))) | ~r1_partfun1('#skF_5', '#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_1('#skF_1'('#skF_4', '#skF_4', '#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_2'('#skF_4', '#skF_4', '#skF_5', '#skF_6')) | ~r1_partfun1('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_19522, c_11205])).
% 14.69/6.54  tff(c_19990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_9890, c_52, c_9891, c_46, c_10197, c_10197, c_19522, c_10263, c_10333, c_19522, c_19690])).
% 14.69/6.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.69/6.54  
% 14.69/6.54  Inference rules
% 14.69/6.54  ----------------------
% 14.69/6.54  #Ref     : 0
% 14.69/6.54  #Sup     : 4143
% 14.69/6.54  #Fact    : 0
% 14.69/6.54  #Define  : 0
% 14.69/6.54  #Split   : 44
% 14.69/6.54  #Chain   : 0
% 14.69/6.54  #Close   : 0
% 14.69/6.54  
% 14.69/6.54  Ordering : KBO
% 14.69/6.54  
% 14.69/6.54  Simplification rules
% 14.69/6.54  ----------------------
% 14.69/6.54  #Subsume      : 1547
% 14.69/6.54  #Demod        : 14828
% 14.69/6.54  #Tautology    : 1062
% 14.69/6.54  #SimpNegUnit  : 558
% 14.69/6.54  #BackRed      : 15
% 14.69/6.54  
% 14.69/6.54  #Partial instantiations: 0
% 14.69/6.54  #Strategies tried      : 1
% 14.69/6.54  
% 14.69/6.54  Timing (in seconds)
% 14.69/6.54  ----------------------
% 14.69/6.54  Preprocessing        : 0.32
% 14.69/6.54  Parsing              : 0.17
% 14.69/6.54  CNF conversion       : 0.02
% 14.69/6.54  Main loop            : 5.41
% 14.69/6.54  Inferencing          : 1.50
% 14.69/6.54  Reduction            : 1.81
% 14.69/6.54  Demodulation         : 1.40
% 14.69/6.54  BG Simplification    : 0.13
% 14.69/6.54  Subsumption          : 1.76
% 14.69/6.54  Abstraction          : 0.20
% 14.69/6.54  MUC search           : 0.00
% 14.69/6.54  Cooper               : 0.00
% 14.69/6.54  Total                : 5.80
% 14.69/6.54  Index Insertion      : 0.00
% 14.69/6.54  Index Deletion       : 0.00
% 14.69/6.54  Index Matching       : 0.00
% 14.69/6.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
