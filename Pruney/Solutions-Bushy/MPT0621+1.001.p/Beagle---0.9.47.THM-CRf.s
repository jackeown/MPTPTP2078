%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0621+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:36 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 243 expanded)
%              Number of leaves         :   26 (  95 expanded)
%              Depth                    :   15
%              Number of atoms          :  168 ( 787 expanded)
%              Number of equality atoms :   94 ( 375 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_relat_1 > o_0_0_xboole_0 > np__1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(np__1,type,(
    np__1: $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_25,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_53,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_41,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_55,axiom,(
    ~ v1_xboole_0(np__1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',spc1_boole)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(c_2,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_25])).

tff(c_4,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_6,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [A_9] : v1_funct_1('#skF_3'(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_9] : k1_relat_1('#skF_3'(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_9] : v1_relat_1('#skF_3'(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_3] : v1_funct_1('#skF_2'(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_3] : k1_relat_1('#skF_2'(A_3)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_3] : v1_relat_1('#skF_2'(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_51,plain,(
    ! [C_29,B_30] :
      ( C_29 = B_30
      | k1_relat_1(C_29) != '#skF_4'
      | k1_relat_1(B_30) != '#skF_4'
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29)
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_55,plain,(
    ! [B_30,A_3] :
      ( B_30 = '#skF_2'(A_3)
      | k1_relat_1('#skF_2'(A_3)) != '#skF_4'
      | k1_relat_1(B_30) != '#skF_4'
      | ~ v1_funct_1('#skF_2'(A_3))
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_14,c_51])).

tff(c_98,plain,(
    ! [B_40,A_41] :
      ( B_40 = '#skF_2'(A_41)
      | A_41 != '#skF_4'
      | k1_relat_1(B_40) != '#skF_4'
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_55])).

tff(c_100,plain,(
    ! [A_9,A_41] :
      ( '#skF_3'(A_9) = '#skF_2'(A_41)
      | A_41 != '#skF_4'
      | k1_relat_1('#skF_3'(A_9)) != '#skF_4'
      | ~ v1_funct_1('#skF_3'(A_9)) ) ),
    inference(resolution,[status(thm)],[c_22,c_98])).

tff(c_110,plain,(
    ! [A_42,A_43] :
      ( '#skF_3'(A_42) = '#skF_2'(A_43)
      | A_43 != '#skF_4'
      | A_42 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_100])).

tff(c_16,plain,(
    ! [A_9,C_14] :
      ( k1_funct_1('#skF_3'(A_9),C_14) = np__1
      | ~ r2_hidden(C_14,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_306,plain,(
    ! [A_58,C_59,A_60] :
      ( k1_funct_1('#skF_2'(A_58),C_59) = np__1
      | ~ r2_hidden(C_59,A_60)
      | A_58 != '#skF_4'
      | A_60 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_16])).

tff(c_382,plain,(
    ! [A_74,A_75,B_76] :
      ( k1_funct_1('#skF_2'(A_74),A_75) = np__1
      | A_74 != '#skF_4'
      | B_76 != '#skF_4'
      | v1_xboole_0(B_76)
      | ~ m1_subset_1(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_26,c_306])).

tff(c_387,plain,(
    ! [A_77,A_78] :
      ( k1_funct_1('#skF_2'(A_77),'#skF_1'(A_78)) = np__1
      | A_77 != '#skF_4'
      | A_78 != '#skF_4'
      | v1_xboole_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_6,c_382])).

tff(c_8,plain,(
    ! [A_3,C_8] :
      ( k1_funct_1('#skF_2'(A_3),C_8) = k1_xboole_0
      | ~ r2_hidden(C_8,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_396,plain,(
    ! [A_78,A_77] :
      ( np__1 = k1_xboole_0
      | ~ r2_hidden('#skF_1'(A_78),A_77)
      | A_77 != '#skF_4'
      | A_78 != '#skF_4'
      | v1_xboole_0(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_8])).

tff(c_426,plain,(
    np__1 = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_396])).

tff(c_24,plain,(
    ~ v1_xboole_0(np__1) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_434,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_24])).

tff(c_437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_434])).

tff(c_439,plain,(
    np__1 != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_396])).

tff(c_53,plain,(
    ! [B_30,A_9] :
      ( B_30 = '#skF_3'(A_9)
      | k1_relat_1('#skF_3'(A_9)) != '#skF_4'
      | k1_relat_1(B_30) != '#skF_4'
      | ~ v1_funct_1('#skF_3'(A_9))
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_22,c_51])).

tff(c_58,plain,(
    ! [B_30,A_9] :
      ( B_30 = '#skF_3'(A_9)
      | k1_relat_1('#skF_3'(A_9)) != '#skF_4'
      | k1_relat_1(B_30) != '#skF_4'
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_53])).

tff(c_156,plain,(
    ! [B_46,A_47] :
      ( B_46 = '#skF_3'(A_47)
      | A_47 != '#skF_4'
      | k1_relat_1(B_46) != '#skF_4'
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_58])).

tff(c_158,plain,(
    ! [A_9,A_47] :
      ( '#skF_3'(A_9) = '#skF_3'(A_47)
      | A_47 != '#skF_4'
      | k1_relat_1('#skF_3'(A_9)) != '#skF_4'
      | ~ v1_funct_1('#skF_3'(A_9)) ) ),
    inference(resolution,[status(thm)],[c_22,c_156])).

tff(c_232,plain,(
    ! [A_51,A_50] :
      ( '#skF_3'(A_51) = '#skF_3'(A_50)
      | A_51 != '#skF_4'
      | A_50 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_158])).

tff(c_301,plain,(
    ! [A_55,C_56,A_57] :
      ( k1_funct_1('#skF_3'(A_55),C_56) = np__1
      | ~ r2_hidden(C_56,A_57)
      | A_57 != '#skF_4'
      | A_55 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_16])).

tff(c_349,plain,(
    ! [A_69,A_70,B_71] :
      ( k1_funct_1('#skF_3'(A_69),A_70) = np__1
      | B_71 != '#skF_4'
      | A_69 != '#skF_4'
      | v1_xboole_0(B_71)
      | ~ m1_subset_1(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_26,c_301])).

tff(c_352,plain,(
    ! [A_69,A_1] :
      ( k1_funct_1('#skF_3'(A_69),'#skF_1'(A_1)) = np__1
      | A_1 != '#skF_4'
      | A_69 != '#skF_4'
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_6,c_349])).

tff(c_311,plain,(
    ! [A_61,C_62,A_63] :
      ( k1_funct_1('#skF_3'(A_61),C_62) = k1_xboole_0
      | ~ r2_hidden(C_62,A_63)
      | A_63 != '#skF_4'
      | A_61 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_8])).

tff(c_448,plain,(
    ! [A_81,A_82,B_83] :
      ( k1_funct_1('#skF_3'(A_81),A_82) = k1_xboole_0
      | B_83 != '#skF_4'
      | A_81 != '#skF_4'
      | v1_xboole_0(B_83)
      | ~ m1_subset_1(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_26,c_311])).

tff(c_453,plain,(
    ! [A_84,A_85] :
      ( k1_funct_1('#skF_3'(A_84),'#skF_1'(A_85)) = k1_xboole_0
      | A_85 != '#skF_4'
      | A_84 != '#skF_4'
      | v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_6,c_448])).

tff(c_468,plain,(
    ! [A_1,A_69] :
      ( np__1 = k1_xboole_0
      | A_1 != '#skF_4'
      | A_69 != '#skF_4'
      | v1_xboole_0(A_1)
      | A_1 != '#skF_4'
      | A_69 != '#skF_4'
      | v1_xboole_0(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_453])).

tff(c_486,plain,(
    ! [A_1,A_69] :
      ( A_1 != '#skF_4'
      | A_69 != '#skF_4'
      | v1_xboole_0(A_1)
      | A_1 != '#skF_4'
      | A_69 != '#skF_4'
      | v1_xboole_0(A_1) ) ),
    inference(negUnitSimplification,[status(thm)],[c_439,c_468])).

tff(c_488,plain,(
    ! [A_69] :
      ( A_69 != '#skF_4'
      | A_69 != '#skF_4' ) ),
    inference(splitLeft,[status(thm)],[c_486])).

tff(c_494,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_488])).

tff(c_495,plain,(
    ! [A_1] :
      ( A_1 != '#skF_4'
      | v1_xboole_0(A_1)
      | A_1 != '#skF_4'
      | v1_xboole_0(A_1) ) ),
    inference(splitRight,[status(thm)],[c_486])).

tff(c_513,plain,(
    ! [A_87] :
      ( A_87 != '#skF_4'
      | v1_xboole_0(A_87) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_495])).

tff(c_28,plain,(
    ! [A_17] :
      ( k1_xboole_0 = A_17
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_522,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_513,c_28])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_533,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_30])).

%------------------------------------------------------------------------------
