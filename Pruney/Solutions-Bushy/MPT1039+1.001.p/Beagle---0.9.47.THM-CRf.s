%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1039+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:18 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 482 expanded)
%              Number of leaves         :   19 ( 167 expanded)
%              Depth                    :   11
%              Number of atoms          :  388 (2512 expanded)
%              Number of equality atoms :   27 ( 524 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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
    '#skF_2': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_2)).

tff(f_62,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_partfun1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_39,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_74,plain,(
    ! [B_33,A_34,C_35,D_36] :
      ( k1_xboole_0 = B_33
      | v1_funct_1('#skF_1'(A_34,B_33,C_35,D_36))
      | ~ r1_partfun1(C_35,D_36)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_33)))
      | ~ v1_funct_1(D_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_34,B_33)))
      | ~ v1_funct_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_76,plain,(
    ! [C_35] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_1('#skF_1'('#skF_2','#skF_3',C_35,'#skF_5'))
      | ~ r1_partfun1(C_35,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_35) ) ),
    inference(resolution,[status(thm)],[c_32,c_74])).

tff(c_81,plain,(
    ! [C_35] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_1('#skF_1'('#skF_2','#skF_3',C_35,'#skF_5'))
      | ~ r1_partfun1(C_35,'#skF_5')
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_76])).

tff(c_87,plain,(
    ! [C_37] :
      ( v1_funct_1('#skF_1'('#skF_2','#skF_3',C_37,'#skF_5'))
      | ~ r1_partfun1(C_37,'#skF_5')
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_37) ) ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_81])).

tff(c_93,plain,
    ( v1_funct_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'))
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_87])).

tff(c_99,plain,(
    v1_funct_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28,c_93])).

tff(c_155,plain,(
    ! [B_45,C_46,A_47,D_48] :
      ( k1_xboole_0 = B_45
      | r1_partfun1(C_46,'#skF_1'(A_47,B_45,C_46,D_48))
      | ~ r1_partfun1(C_46,D_48)
      | ~ m1_subset_1(D_48,k1_zfmisc_1(k2_zfmisc_1(A_47,B_45)))
      | ~ v1_funct_1(D_48)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_45)))
      | ~ v1_funct_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_157,plain,(
    ! [C_46] :
      ( k1_xboole_0 = '#skF_3'
      | r1_partfun1(C_46,'#skF_1'('#skF_2','#skF_3',C_46,'#skF_5'))
      | ~ r1_partfun1(C_46,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_46) ) ),
    inference(resolution,[status(thm)],[c_32,c_155])).

tff(c_162,plain,(
    ! [C_46] :
      ( k1_xboole_0 = '#skF_3'
      | r1_partfun1(C_46,'#skF_1'('#skF_2','#skF_3',C_46,'#skF_5'))
      | ~ r1_partfun1(C_46,'#skF_5')
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_157])).

tff(c_168,plain,(
    ! [C_49] :
      ( r1_partfun1(C_49,'#skF_1'('#skF_2','#skF_3',C_49,'#skF_5'))
      | ~ r1_partfun1(C_49,'#skF_5')
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_49) ) ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_162])).

tff(c_172,plain,
    ( r1_partfun1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'))
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_168])).

tff(c_178,plain,(
    r1_partfun1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28,c_172])).

tff(c_190,plain,(
    ! [B_51,D_52,A_53,C_54] :
      ( k1_xboole_0 = B_51
      | r1_partfun1(D_52,'#skF_1'(A_53,B_51,C_54,D_52))
      | ~ r1_partfun1(C_54,D_52)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_51)))
      | ~ v1_funct_1(D_52)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_53,B_51)))
      | ~ v1_funct_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_192,plain,(
    ! [C_54] :
      ( k1_xboole_0 = '#skF_3'
      | r1_partfun1('#skF_5','#skF_1'('#skF_2','#skF_3',C_54,'#skF_5'))
      | ~ r1_partfun1(C_54,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_54) ) ),
    inference(resolution,[status(thm)],[c_32,c_190])).

tff(c_197,plain,(
    ! [C_54] :
      ( k1_xboole_0 = '#skF_3'
      | r1_partfun1('#skF_5','#skF_1'('#skF_2','#skF_3',C_54,'#skF_5'))
      | ~ r1_partfun1(C_54,'#skF_5')
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_192])).

tff(c_203,plain,(
    ! [C_55] :
      ( r1_partfun1('#skF_5','#skF_1'('#skF_2','#skF_3',C_55,'#skF_5'))
      | ~ r1_partfun1(C_55,'#skF_5')
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_55) ) ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_197])).

tff(c_209,plain,
    ( r1_partfun1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'))
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_203])).

tff(c_215,plain,(
    r1_partfun1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28,c_209])).

tff(c_101,plain,(
    ! [B_38,A_39,C_40,D_41] :
      ( k1_xboole_0 = B_38
      | v1_partfun1('#skF_1'(A_39,B_38,C_40,D_41),A_39)
      | ~ r1_partfun1(C_40,D_41)
      | ~ m1_subset_1(D_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_38)))
      | ~ v1_funct_1(D_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_39,B_38)))
      | ~ v1_funct_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_103,plain,(
    ! [C_40] :
      ( k1_xboole_0 = '#skF_3'
      | v1_partfun1('#skF_1'('#skF_2','#skF_3',C_40,'#skF_5'),'#skF_2')
      | ~ r1_partfun1(C_40,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_40) ) ),
    inference(resolution,[status(thm)],[c_32,c_101])).

tff(c_108,plain,(
    ! [C_40] :
      ( k1_xboole_0 = '#skF_3'
      | v1_partfun1('#skF_1'('#skF_2','#skF_3',C_40,'#skF_5'),'#skF_2')
      | ~ r1_partfun1(C_40,'#skF_5')
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_103])).

tff(c_129,plain,(
    ! [C_43] :
      ( v1_partfun1('#skF_1'('#skF_2','#skF_3',C_43,'#skF_5'),'#skF_2')
      | ~ r1_partfun1(C_43,'#skF_5')
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_43) ) ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_108])).

tff(c_135,plain,
    ( v1_partfun1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2')
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_129])).

tff(c_141,plain,(
    v1_partfun1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28,c_135])).

tff(c_258,plain,(
    ! [B_60,A_61,C_62,D_63] :
      ( k1_xboole_0 = B_60
      | m1_subset_1('#skF_1'(A_61,B_60,C_62,D_63),k1_zfmisc_1(k2_zfmisc_1(A_61,B_60)))
      | ~ r1_partfun1(C_62,D_63)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60)))
      | ~ v1_funct_1(D_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60)))
      | ~ v1_funct_1(C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_funct_2(C_3,A_1,B_2)
      | ~ v1_partfun1(C_3,A_1)
      | ~ v1_funct_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_360,plain,(
    ! [A_67,B_68,C_69,D_70] :
      ( v1_funct_2('#skF_1'(A_67,B_68,C_69,D_70),A_67,B_68)
      | ~ v1_partfun1('#skF_1'(A_67,B_68,C_69,D_70),A_67)
      | ~ v1_funct_1('#skF_1'(A_67,B_68,C_69,D_70))
      | k1_xboole_0 = B_68
      | ~ r1_partfun1(C_69,D_70)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_1(D_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_1(C_69) ) ),
    inference(resolution,[status(thm)],[c_258,c_2])).

tff(c_366,plain,(
    ! [C_69] :
      ( v1_funct_2('#skF_1'('#skF_2','#skF_3',C_69,'#skF_5'),'#skF_2','#skF_3')
      | ~ v1_partfun1('#skF_1'('#skF_2','#skF_3',C_69,'#skF_5'),'#skF_2')
      | ~ v1_funct_1('#skF_1'('#skF_2','#skF_3',C_69,'#skF_5'))
      | k1_xboole_0 = '#skF_3'
      | ~ r1_partfun1(C_69,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_69) ) ),
    inference(resolution,[status(thm)],[c_32,c_360])).

tff(c_373,plain,(
    ! [C_69] :
      ( v1_funct_2('#skF_1'('#skF_2','#skF_3',C_69,'#skF_5'),'#skF_2','#skF_3')
      | ~ v1_partfun1('#skF_1'('#skF_2','#skF_3',C_69,'#skF_5'),'#skF_2')
      | ~ v1_funct_1('#skF_1'('#skF_2','#skF_3',C_69,'#skF_5'))
      | k1_xboole_0 = '#skF_3'
      | ~ r1_partfun1(C_69,'#skF_5')
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_366])).

tff(c_379,plain,(
    ! [C_71] :
      ( v1_funct_2('#skF_1'('#skF_2','#skF_3',C_71,'#skF_5'),'#skF_2','#skF_3')
      | ~ v1_partfun1('#skF_1'('#skF_2','#skF_3',C_71,'#skF_5'),'#skF_2')
      | ~ v1_funct_1('#skF_1'('#skF_2','#skF_3',C_71,'#skF_5'))
      | ~ r1_partfun1(C_71,'#skF_5')
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_71) ) ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_373])).

tff(c_389,plain,
    ( v1_funct_2('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_partfun1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_funct_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'))
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_379])).

tff(c_398,plain,(
    v1_funct_2('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28,c_99,c_141,c_389])).

tff(c_26,plain,(
    ! [E_16] :
      ( ~ r1_partfun1('#skF_5',E_16)
      | ~ r1_partfun1('#skF_4',E_16)
      | ~ m1_subset_1(E_16,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2(E_16,'#skF_2','#skF_3')
      | ~ v1_funct_1(E_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_312,plain,(
    ! [C_62,D_63] :
      ( ~ r1_partfun1('#skF_5','#skF_1'('#skF_2','#skF_3',C_62,D_63))
      | ~ r1_partfun1('#skF_4','#skF_1'('#skF_2','#skF_3',C_62,D_63))
      | ~ v1_funct_2('#skF_1'('#skF_2','#skF_3',C_62,D_63),'#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_1'('#skF_2','#skF_3',C_62,D_63))
      | k1_xboole_0 = '#skF_3'
      | ~ r1_partfun1(C_62,D_63)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(D_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_62) ) ),
    inference(resolution,[status(thm)],[c_258,c_26])).

tff(c_477,plain,(
    ! [C_77,D_78] :
      ( ~ r1_partfun1('#skF_5','#skF_1'('#skF_2','#skF_3',C_77,D_78))
      | ~ r1_partfun1('#skF_4','#skF_1'('#skF_2','#skF_3',C_77,D_78))
      | ~ v1_funct_2('#skF_1'('#skF_2','#skF_3',C_77,D_78),'#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_1'('#skF_2','#skF_3',C_77,D_78))
      | ~ r1_partfun1(C_77,D_78)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(D_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_77) ) ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_312])).

tff(c_479,plain,
    ( ~ r1_partfun1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'))
    | ~ r1_partfun1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'))
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_398,c_477])).

tff(c_483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_99,c_178,c_215,c_479])).

tff(c_485,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_484,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_490,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_484])).

tff(c_499,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_36])).

tff(c_500,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_32])).

tff(c_22,plain,(
    ! [B_5,C_6,D_10] :
      ( v1_funct_1('#skF_1'(k1_xboole_0,B_5,C_6,D_10))
      | ~ r1_partfun1(C_6,D_10)
      | ~ m1_subset_1(D_10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5)))
      | ~ v1_funct_1(D_10)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5)))
      | ~ v1_funct_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_533,plain,(
    ! [B_83,C_84,D_85] :
      ( v1_funct_1('#skF_1'('#skF_3',B_83,C_84,D_85))
      | ~ r1_partfun1(C_84,D_85)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_83)))
      | ~ v1_funct_1(D_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_83)))
      | ~ v1_funct_1(C_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_485,c_485,c_22])).

tff(c_535,plain,(
    ! [C_84] :
      ( v1_funct_1('#skF_1'('#skF_3','#skF_3',C_84,'#skF_5'))
      | ~ r1_partfun1(C_84,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_1(C_84) ) ),
    inference(resolution,[status(thm)],[c_500,c_533])).

tff(c_544,plain,(
    ! [C_86] :
      ( v1_funct_1('#skF_1'('#skF_3','#skF_3',C_86,'#skF_5'))
      | ~ r1_partfun1(C_86,'#skF_5')
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_1(C_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_535])).

tff(c_550,plain,
    ( v1_funct_1('#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'))
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_499,c_544])).

tff(c_556,plain,(
    v1_funct_1('#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28,c_550])).

tff(c_10,plain,(
    ! [C_6,B_5,D_10] :
      ( r1_partfun1(C_6,'#skF_1'(k1_xboole_0,B_5,C_6,D_10))
      | ~ r1_partfun1(C_6,D_10)
      | ~ m1_subset_1(D_10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5)))
      | ~ v1_funct_1(D_10)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5)))
      | ~ v1_funct_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_612,plain,(
    ! [C_93,B_94,D_95] :
      ( r1_partfun1(C_93,'#skF_1'('#skF_3',B_94,C_93,D_95))
      | ~ r1_partfun1(C_93,D_95)
      | ~ m1_subset_1(D_95,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_94)))
      | ~ v1_funct_1(D_95)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_94)))
      | ~ v1_funct_1(C_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_485,c_485,c_10])).

tff(c_614,plain,(
    ! [C_93] :
      ( r1_partfun1(C_93,'#skF_1'('#skF_3','#skF_3',C_93,'#skF_5'))
      | ~ r1_partfun1(C_93,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_1(C_93) ) ),
    inference(resolution,[status(thm)],[c_500,c_612])).

tff(c_623,plain,(
    ! [C_96] :
      ( r1_partfun1(C_96,'#skF_1'('#skF_3','#skF_3',C_96,'#skF_5'))
      | ~ r1_partfun1(C_96,'#skF_5')
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_1(C_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_614])).

tff(c_627,plain,
    ( r1_partfun1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'))
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_499,c_623])).

tff(c_633,plain,(
    r1_partfun1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28,c_627])).

tff(c_6,plain,(
    ! [D_10,B_5,C_6] :
      ( r1_partfun1(D_10,'#skF_1'(k1_xboole_0,B_5,C_6,D_10))
      | ~ r1_partfun1(C_6,D_10)
      | ~ m1_subset_1(D_10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5)))
      | ~ v1_funct_1(D_10)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5)))
      | ~ v1_funct_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_559,plain,(
    ! [D_87,B_88,C_89] :
      ( r1_partfun1(D_87,'#skF_1'('#skF_3',B_88,C_89,D_87))
      | ~ r1_partfun1(C_89,D_87)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_88)))
      | ~ v1_funct_1(D_87)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_88)))
      | ~ v1_funct_1(C_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_485,c_485,c_6])).

tff(c_561,plain,(
    ! [C_89] :
      ( r1_partfun1('#skF_5','#skF_1'('#skF_3','#skF_3',C_89,'#skF_5'))
      | ~ r1_partfun1(C_89,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_1(C_89) ) ),
    inference(resolution,[status(thm)],[c_500,c_559])).

tff(c_598,plain,(
    ! [C_92] :
      ( r1_partfun1('#skF_5','#skF_1'('#skF_3','#skF_3',C_92,'#skF_5'))
      | ~ r1_partfun1(C_92,'#skF_5')
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_1(C_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_561])).

tff(c_604,plain,
    ( r1_partfun1('#skF_5','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'))
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_499,c_598])).

tff(c_610,plain,(
    r1_partfun1('#skF_5','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28,c_604])).

tff(c_14,plain,(
    ! [B_5,C_6,D_10] :
      ( v1_partfun1('#skF_1'(k1_xboole_0,B_5,C_6,D_10),k1_xboole_0)
      | ~ r1_partfun1(C_6,D_10)
      | ~ m1_subset_1(D_10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5)))
      | ~ v1_funct_1(D_10)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5)))
      | ~ v1_funct_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_646,plain,(
    ! [B_98,C_99,D_100] :
      ( v1_partfun1('#skF_1'('#skF_3',B_98,C_99,D_100),'#skF_3')
      | ~ r1_partfun1(C_99,D_100)
      | ~ m1_subset_1(D_100,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_98)))
      | ~ v1_funct_1(D_100)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_98)))
      | ~ v1_funct_1(C_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_485,c_485,c_485,c_14])).

tff(c_648,plain,(
    ! [C_99] :
      ( v1_partfun1('#skF_1'('#skF_3','#skF_3',C_99,'#skF_5'),'#skF_3')
      | ~ r1_partfun1(C_99,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_1(C_99) ) ),
    inference(resolution,[status(thm)],[c_500,c_646])).

tff(c_657,plain,(
    ! [C_101] :
      ( v1_partfun1('#skF_1'('#skF_3','#skF_3',C_101,'#skF_5'),'#skF_3')
      | ~ r1_partfun1(C_101,'#skF_5')
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_1(C_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_648])).

tff(c_663,plain,
    ( v1_partfun1('#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_499,c_657])).

tff(c_669,plain,(
    v1_partfun1('#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28,c_663])).

tff(c_18,plain,(
    ! [B_5,C_6,D_10] :
      ( m1_subset_1('#skF_1'(k1_xboole_0,B_5,C_6,D_10),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5)))
      | ~ r1_partfun1(C_6,D_10)
      | ~ m1_subset_1(D_10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5)))
      | ~ v1_funct_1(D_10)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5)))
      | ~ v1_funct_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_732,plain,(
    ! [B_119,C_120,D_121] :
      ( m1_subset_1('#skF_1'('#skF_3',B_119,C_120,D_121),k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_119)))
      | ~ r1_partfun1(C_120,D_121)
      | ~ m1_subset_1(D_121,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_119)))
      | ~ v1_funct_1(D_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_119)))
      | ~ v1_funct_1(C_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_485,c_485,c_485,c_18])).

tff(c_891,plain,(
    ! [B_128,C_129,D_130] :
      ( v1_funct_2('#skF_1'('#skF_3',B_128,C_129,D_130),'#skF_3',B_128)
      | ~ v1_partfun1('#skF_1'('#skF_3',B_128,C_129,D_130),'#skF_3')
      | ~ v1_funct_1('#skF_1'('#skF_3',B_128,C_129,D_130))
      | ~ r1_partfun1(C_129,D_130)
      | ~ m1_subset_1(D_130,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_128)))
      | ~ v1_funct_1(D_130)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_128)))
      | ~ v1_funct_1(C_129) ) ),
    inference(resolution,[status(thm)],[c_732,c_2])).

tff(c_898,plain,(
    ! [C_129] :
      ( v1_funct_2('#skF_1'('#skF_3','#skF_3',C_129,'#skF_5'),'#skF_3','#skF_3')
      | ~ v1_partfun1('#skF_1'('#skF_3','#skF_3',C_129,'#skF_5'),'#skF_3')
      | ~ v1_funct_1('#skF_1'('#skF_3','#skF_3',C_129,'#skF_5'))
      | ~ r1_partfun1(C_129,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_1(C_129) ) ),
    inference(resolution,[status(thm)],[c_500,c_891])).

tff(c_909,plain,(
    ! [C_131] :
      ( v1_funct_2('#skF_1'('#skF_3','#skF_3',C_131,'#skF_5'),'#skF_3','#skF_3')
      | ~ v1_partfun1('#skF_1'('#skF_3','#skF_3',C_131,'#skF_5'),'#skF_3')
      | ~ v1_funct_1('#skF_1'('#skF_3','#skF_3',C_131,'#skF_5'))
      | ~ r1_partfun1(C_131,'#skF_5')
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_1(C_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_898])).

tff(c_923,plain,
    ( v1_funct_2('#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_3')
    | ~ v1_partfun1('#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v1_funct_1('#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'))
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_499,c_909])).

tff(c_932,plain,(
    v1_funct_2('#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28,c_556,c_669,c_923])).

tff(c_516,plain,(
    ! [E_16] :
      ( ~ r1_partfun1('#skF_5',E_16)
      | ~ r1_partfun1('#skF_4',E_16)
      | ~ m1_subset_1(E_16,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_2(E_16,'#skF_3','#skF_3')
      | ~ v1_funct_1(E_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_490,c_26])).

tff(c_802,plain,(
    ! [C_120,D_121] :
      ( ~ r1_partfun1('#skF_5','#skF_1'('#skF_3','#skF_3',C_120,D_121))
      | ~ r1_partfun1('#skF_4','#skF_1'('#skF_3','#skF_3',C_120,D_121))
      | ~ v1_funct_2('#skF_1'('#skF_3','#skF_3',C_120,D_121),'#skF_3','#skF_3')
      | ~ v1_funct_1('#skF_1'('#skF_3','#skF_3',C_120,D_121))
      | ~ r1_partfun1(C_120,D_121)
      | ~ m1_subset_1(D_121,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_1(D_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_1(C_120) ) ),
    inference(resolution,[status(thm)],[c_732,c_516])).

tff(c_934,plain,
    ( ~ r1_partfun1('#skF_5','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'))
    | ~ r1_partfun1('#skF_4','#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_1'('#skF_3','#skF_3','#skF_4','#skF_5'))
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_932,c_802])).

tff(c_938,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_499,c_34,c_500,c_28,c_556,c_633,c_610,c_934])).

%------------------------------------------------------------------------------
