%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:26 EST 2020

% Result     : Theorem 7.22s
% Output     : CNFRefutation 7.22s
% Verified   : 
% Statistics : Number of formulae       :  165 (1453 expanded)
%              Number of leaves         :   40 ( 524 expanded)
%              Depth                    :   25
%              Number of atoms          :  423 (6051 expanded)
%              Number of equality atoms :  165 (2115 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_192,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_105,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_107,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_83,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_38,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_166,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_150,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
              & k2_relset_1(A,B,D) = B )
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | ( v2_funct_1(D)
                & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_274,plain,(
    ! [B_87,A_88,F_89,E_91,D_86,C_90] :
      ( k1_partfun1(A_88,B_87,C_90,D_86,E_91,F_89) = k5_relat_1(E_91,F_89)
      | ~ m1_subset_1(F_89,k1_zfmisc_1(k2_zfmisc_1(C_90,D_86)))
      | ~ v1_funct_1(F_89)
      | ~ m1_subset_1(E_91,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87)))
      | ~ v1_funct_1(E_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_280,plain,(
    ! [A_88,B_87,E_91] :
      ( k1_partfun1(A_88,B_87,'#skF_2','#skF_1',E_91,'#skF_4') = k5_relat_1(E_91,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_91,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87)))
      | ~ v1_funct_1(E_91) ) ),
    inference(resolution,[status(thm)],[c_62,c_274])).

tff(c_422,plain,(
    ! [A_111,B_112,E_113] :
      ( k1_partfun1(A_111,B_112,'#skF_2','#skF_1',E_113,'#skF_4') = k5_relat_1(E_113,'#skF_4')
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ v1_funct_1(E_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_280])).

tff(c_428,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_422])).

tff(c_435,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_428])).

tff(c_34,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_26,plain,(
    ! [A_19] : m1_subset_1(k6_relat_1(A_19),k1_zfmisc_1(k2_zfmisc_1(A_19,A_19))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_73,plain,(
    ! [A_19] : m1_subset_1(k6_partfun1(A_19),k1_zfmisc_1(k2_zfmisc_1(A_19,A_19))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_26])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_194,plain,(
    ! [D_68,C_69,A_70,B_71] :
      ( D_68 = C_69
      | ~ r2_relset_1(A_70,B_71,C_69,D_68)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_202,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_194])).

tff(c_217,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_202])).

tff(c_218,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_441,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_218])).

tff(c_452,plain,(
    ! [B_115,D_116,C_114,E_117,A_118,F_119] :
      ( m1_subset_1(k1_partfun1(A_118,B_115,C_114,D_116,E_117,F_119),k1_zfmisc_1(k2_zfmisc_1(A_118,D_116)))
      | ~ m1_subset_1(F_119,k1_zfmisc_1(k2_zfmisc_1(C_114,D_116)))
      | ~ v1_funct_1(F_119)
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1(A_118,B_115)))
      | ~ v1_funct_1(E_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_483,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_452])).

tff(c_504,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_483])).

tff(c_506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_441,c_504])).

tff(c_507,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_554,plain,(
    ! [E_127,F_129,B_125,D_126,A_128,C_124] :
      ( v1_funct_1(k1_partfun1(A_128,B_125,C_124,D_126,E_127,F_129))
      | ~ m1_subset_1(F_129,k1_zfmisc_1(k2_zfmisc_1(C_124,D_126)))
      | ~ v1_funct_1(F_129)
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_125)))
      | ~ v1_funct_1(E_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_560,plain,(
    ! [A_128,B_125,E_127] :
      ( v1_funct_1(k1_partfun1(A_128,B_125,'#skF_2','#skF_1',E_127,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_125)))
      | ~ v1_funct_1(E_127) ) ),
    inference(resolution,[status(thm)],[c_62,c_554])).

tff(c_585,plain,(
    ! [A_133,B_134,E_135] :
      ( v1_funct_1(k1_partfun1(A_133,B_134,'#skF_2','#skF_1',E_135,'#skF_4'))
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134)))
      | ~ v1_funct_1(E_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_560])).

tff(c_591,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_585])).

tff(c_598,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_507,c_591])).

tff(c_8,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_77,plain,(
    ! [A_6] : k2_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_8])).

tff(c_10,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,(
    ! [A_7] : v1_relat_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_114,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_120,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_114])).

tff(c_129,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_120])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_143,plain,(
    ! [A_61,B_62,C_63] :
      ( k2_relset_1(A_61,B_62,C_63) = k2_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_149,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_143])).

tff(c_156,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_149])).

tff(c_18,plain,(
    ! [A_9,B_11] :
      ( k2_funct_1(A_9) = B_11
      | k6_relat_1(k2_relat_1(A_9)) != k5_relat_1(B_11,A_9)
      | k2_relat_1(B_11) != k1_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_516,plain,(
    ! [A_120,B_121] :
      ( k2_funct_1(A_120) = B_121
      | k6_partfun1(k2_relat_1(A_120)) != k5_relat_1(B_121,A_120)
      | k2_relat_1(B_121) != k1_relat_1(A_120)
      | ~ v2_funct_1(A_120)
      | ~ v1_funct_1(B_121)
      | ~ v1_relat_1(B_121)
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_18])).

tff(c_520,plain,(
    ! [B_121] :
      ( k2_funct_1('#skF_3') = B_121
      | k5_relat_1(B_121,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_121) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_121)
      | ~ v1_relat_1(B_121)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_516])).

tff(c_527,plain,(
    ! [B_122] :
      ( k2_funct_1('#skF_3') = B_122
      | k5_relat_1(B_122,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_122) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_122)
      | ~ v1_relat_1(B_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_72,c_56,c_520])).

tff(c_539,plain,(
    ! [A_7] :
      ( k6_partfun1(A_7) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_7),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_7)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_76,c_527])).

tff(c_549,plain,(
    ! [A_7] :
      ( k6_partfun1(A_7) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_7),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_7
      | ~ v1_funct_1(k6_partfun1(A_7)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_539])).

tff(c_605,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_598,c_549])).

tff(c_608,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_605])).

tff(c_6,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_78,plain,(
    ! [A_6] : k1_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_679,plain,(
    ! [A_151,C_152,B_153] :
      ( k6_partfun1(A_151) = k5_relat_1(C_152,k2_funct_1(C_152))
      | k1_xboole_0 = B_153
      | ~ v2_funct_1(C_152)
      | k2_relset_1(A_151,B_153,C_152) != B_153
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_151,B_153)))
      | ~ v1_funct_2(C_152,A_151,B_153)
      | ~ v1_funct_1(C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_683,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_679])).

tff(c_691,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_683])).

tff(c_692,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_691])).

tff(c_16,plain,(
    ! [A_8] :
      ( k1_relat_1(k5_relat_1(A_8,k2_funct_1(A_8))) = k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_700,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_692,c_16])).

tff(c_707,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_72,c_56,c_78,c_700])).

tff(c_709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_608,c_707])).

tff(c_711,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_605])).

tff(c_50,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_123,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_114])).

tff(c_132,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_123])).

tff(c_530,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_132,c_527])).

tff(c_542,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_530])).

tff(c_543,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_542])).

tff(c_550,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_543])).

tff(c_714,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_711,c_550])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_133,plain,(
    ! [A_58,B_59,D_60] :
      ( r2_relset_1(A_58,B_59,D_60,D_60)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_140,plain,(
    ! [A_19] : r2_relset_1(A_19,A_19,k6_partfun1(A_19),k6_partfun1(A_19)) ),
    inference(resolution,[status(thm)],[c_73,c_133])).

tff(c_157,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_143])).

tff(c_1469,plain,(
    ! [A_216,B_217,C_218,D_219] :
      ( k2_relset_1(A_216,B_217,C_218) = B_217
      | ~ r2_relset_1(B_217,B_217,k1_partfun1(B_217,A_216,A_216,B_217,D_219,C_218),k6_partfun1(B_217))
      | ~ m1_subset_1(D_219,k1_zfmisc_1(k2_zfmisc_1(B_217,A_216)))
      | ~ v1_funct_2(D_219,B_217,A_216)
      | ~ v1_funct_1(D_219)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217)))
      | ~ v1_funct_2(C_218,A_216,B_217)
      | ~ v1_funct_1(C_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1475,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_507,c_1469])).

tff(c_1479,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_140,c_157,c_1475])).

tff(c_1481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_714,c_1479])).

tff(c_1482,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_543])).

tff(c_2436,plain,(
    ! [E_330,C_329,F_328,D_325,A_327,B_326] :
      ( k1_partfun1(A_327,B_326,C_329,D_325,E_330,F_328) = k5_relat_1(E_330,F_328)
      | ~ m1_subset_1(F_328,k1_zfmisc_1(k2_zfmisc_1(C_329,D_325)))
      | ~ v1_funct_1(F_328)
      | ~ m1_subset_1(E_330,k1_zfmisc_1(k2_zfmisc_1(A_327,B_326)))
      | ~ v1_funct_1(E_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2442,plain,(
    ! [A_327,B_326,E_330] :
      ( k1_partfun1(A_327,B_326,'#skF_2','#skF_1',E_330,'#skF_4') = k5_relat_1(E_330,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_330,k1_zfmisc_1(k2_zfmisc_1(A_327,B_326)))
      | ~ v1_funct_1(E_330) ) ),
    inference(resolution,[status(thm)],[c_62,c_2436])).

tff(c_2679,plain,(
    ! [A_352,B_353,E_354] :
      ( k1_partfun1(A_352,B_353,'#skF_2','#skF_1',E_354,'#skF_4') = k5_relat_1(E_354,'#skF_4')
      | ~ m1_subset_1(E_354,k1_zfmisc_1(k2_zfmisc_1(A_352,B_353)))
      | ~ v1_funct_1(E_354) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2442])).

tff(c_2685,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2679])).

tff(c_2692,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_507,c_2685])).

tff(c_1483,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_543])).

tff(c_74,plain,(
    ! [A_9,B_11] :
      ( k2_funct_1(A_9) = B_11
      | k6_partfun1(k2_relat_1(A_9)) != k5_relat_1(B_11,A_9)
      | k2_relat_1(B_11) != k1_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_18])).

tff(c_1487,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_11,'#skF_4')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1483,c_74])).

tff(c_1491,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_11,'#skF_4')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_66,c_1487])).

tff(c_1499,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1491])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_12,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_75,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12])).

tff(c_2382,plain,(
    ! [E_309,D_308,B_306,C_307,A_305] :
      ( k1_xboole_0 = C_307
      | v2_funct_1(E_309)
      | k2_relset_1(A_305,B_306,D_308) != B_306
      | ~ v2_funct_1(k1_partfun1(A_305,B_306,B_306,C_307,D_308,E_309))
      | ~ m1_subset_1(E_309,k1_zfmisc_1(k2_zfmisc_1(B_306,C_307)))
      | ~ v1_funct_2(E_309,B_306,C_307)
      | ~ v1_funct_1(E_309)
      | ~ m1_subset_1(D_308,k1_zfmisc_1(k2_zfmisc_1(A_305,B_306)))
      | ~ v1_funct_2(D_308,A_305,B_306)
      | ~ v1_funct_1(D_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2388,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_507,c_2382])).

tff(c_2396,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_64,c_62,c_75,c_60,c_2388])).

tff(c_2398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1499,c_54,c_2396])).

tff(c_2400,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1491])).

tff(c_1484,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1483,c_157])).

tff(c_2499,plain,(
    ! [B_338,C_339,A_340] :
      ( k6_partfun1(B_338) = k5_relat_1(k2_funct_1(C_339),C_339)
      | k1_xboole_0 = B_338
      | ~ v2_funct_1(C_339)
      | k2_relset_1(A_340,B_338,C_339) != B_338
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(A_340,B_338)))
      | ~ v1_funct_2(C_339,A_340,B_338)
      | ~ v1_funct_1(C_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2505,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_2499])).

tff(c_2515,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1484,c_2400,c_2505])).

tff(c_2516,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2515])).

tff(c_2526,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2516])).

tff(c_2557,plain,(
    ! [A_345,C_346,B_347] :
      ( k6_partfun1(A_345) = k5_relat_1(C_346,k2_funct_1(C_346))
      | k1_xboole_0 = B_347
      | ~ v2_funct_1(C_346)
      | k2_relset_1(A_345,B_347,C_346) != B_347
      | ~ m1_subset_1(C_346,k1_zfmisc_1(k2_zfmisc_1(A_345,B_347)))
      | ~ v1_funct_2(C_346,A_345,B_347)
      | ~ v1_funct_1(C_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2561,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2557])).

tff(c_2569,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_2561])).

tff(c_2570,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2569])).

tff(c_2578,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2570,c_16])).

tff(c_2585,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_72,c_56,c_78,c_2578])).

tff(c_2587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2526,c_2585])).

tff(c_2589,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2516])).

tff(c_2594,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2589,c_1484])).

tff(c_2629,plain,(
    ! [A_349,C_350,B_351] :
      ( k6_partfun1(A_349) = k5_relat_1(C_350,k2_funct_1(C_350))
      | k1_xboole_0 = B_351
      | ~ v2_funct_1(C_350)
      | k2_relset_1(A_349,B_351,C_350) != B_351
      | ~ m1_subset_1(C_350,k1_zfmisc_1(k2_zfmisc_1(A_349,B_351)))
      | ~ v1_funct_2(C_350,A_349,B_351)
      | ~ v1_funct_1(C_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2635,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_2629])).

tff(c_2645,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_2594,c_2400,c_2635])).

tff(c_2646,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2645])).

tff(c_2664,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2646,c_16])).

tff(c_2671,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_66,c_2400,c_78,c_2664])).

tff(c_2399,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_11,'#skF_4')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(splitRight,[status(thm)],[c_1491])).

tff(c_2591,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k5_relat_1(B_11,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2589,c_2399])).

tff(c_4728,plain,(
    ! [B_451] :
      ( k2_funct_1('#skF_4') = B_451
      | k5_relat_1(B_451,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_451) != '#skF_2'
      | ~ v1_funct_1(B_451)
      | ~ v1_relat_1(B_451) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2671,c_2591])).

tff(c_4821,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_4728])).

tff(c_4916,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_156,c_2692,c_4821])).

tff(c_4921,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4916,c_2646])).

tff(c_4924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1482,c_4921])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:13:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.22/2.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.22/2.64  
% 7.22/2.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.22/2.64  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.22/2.64  
% 7.22/2.64  %Foreground sorts:
% 7.22/2.64  
% 7.22/2.64  
% 7.22/2.64  %Background operators:
% 7.22/2.64  
% 7.22/2.64  
% 7.22/2.64  %Foreground operators:
% 7.22/2.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.22/2.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.22/2.64  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.22/2.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.22/2.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.22/2.64  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.22/2.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.22/2.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.22/2.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.22/2.64  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.22/2.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.22/2.64  tff('#skF_2', type, '#skF_2': $i).
% 7.22/2.64  tff('#skF_3', type, '#skF_3': $i).
% 7.22/2.64  tff('#skF_1', type, '#skF_1': $i).
% 7.22/2.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.22/2.64  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.22/2.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.22/2.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.22/2.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.22/2.64  tff('#skF_4', type, '#skF_4': $i).
% 7.22/2.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.22/2.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.22/2.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.22/2.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.22/2.64  
% 7.22/2.67  tff(f_192, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 7.22/2.67  tff(f_105, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.22/2.67  tff(f_107, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.22/2.67  tff(f_83, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 7.22/2.67  tff(f_81, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.22/2.67  tff(f_95, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.22/2.67  tff(f_38, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.22/2.67  tff(f_42, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.22/2.67  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.22/2.67  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.22/2.67  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.22/2.67  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 7.22/2.67  tff(f_166, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 7.22/2.67  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 7.22/2.67  tff(f_124, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.22/2.67  tff(f_150, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 7.22/2.67  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.22/2.67  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.22/2.67  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.22/2.67  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.22/2.67  tff(c_274, plain, (![B_87, A_88, F_89, E_91, D_86, C_90]: (k1_partfun1(A_88, B_87, C_90, D_86, E_91, F_89)=k5_relat_1(E_91, F_89) | ~m1_subset_1(F_89, k1_zfmisc_1(k2_zfmisc_1(C_90, D_86))) | ~v1_funct_1(F_89) | ~m1_subset_1(E_91, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))) | ~v1_funct_1(E_91))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.22/2.67  tff(c_280, plain, (![A_88, B_87, E_91]: (k1_partfun1(A_88, B_87, '#skF_2', '#skF_1', E_91, '#skF_4')=k5_relat_1(E_91, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_91, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))) | ~v1_funct_1(E_91))), inference(resolution, [status(thm)], [c_62, c_274])).
% 7.22/2.67  tff(c_422, plain, (![A_111, B_112, E_113]: (k1_partfun1(A_111, B_112, '#skF_2', '#skF_1', E_113, '#skF_4')=k5_relat_1(E_113, '#skF_4') | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~v1_funct_1(E_113))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_280])).
% 7.22/2.67  tff(c_428, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_422])).
% 7.22/2.67  tff(c_435, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_428])).
% 7.22/2.67  tff(c_34, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.22/2.67  tff(c_26, plain, (![A_19]: (m1_subset_1(k6_relat_1(A_19), k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.22/2.67  tff(c_73, plain, (![A_19]: (m1_subset_1(k6_partfun1(A_19), k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_26])).
% 7.22/2.67  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.22/2.67  tff(c_194, plain, (![D_68, C_69, A_70, B_71]: (D_68=C_69 | ~r2_relset_1(A_70, B_71, C_69, D_68) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.22/2.67  tff(c_202, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_194])).
% 7.22/2.67  tff(c_217, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_202])).
% 7.22/2.67  tff(c_218, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_217])).
% 7.22/2.67  tff(c_441, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_218])).
% 7.22/2.67  tff(c_452, plain, (![B_115, D_116, C_114, E_117, A_118, F_119]: (m1_subset_1(k1_partfun1(A_118, B_115, C_114, D_116, E_117, F_119), k1_zfmisc_1(k2_zfmisc_1(A_118, D_116))) | ~m1_subset_1(F_119, k1_zfmisc_1(k2_zfmisc_1(C_114, D_116))) | ~v1_funct_1(F_119) | ~m1_subset_1(E_117, k1_zfmisc_1(k2_zfmisc_1(A_118, B_115))) | ~v1_funct_1(E_117))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.22/2.67  tff(c_483, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_435, c_452])).
% 7.22/2.67  tff(c_504, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_483])).
% 7.22/2.67  tff(c_506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_441, c_504])).
% 7.22/2.67  tff(c_507, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_217])).
% 7.22/2.67  tff(c_554, plain, (![E_127, F_129, B_125, D_126, A_128, C_124]: (v1_funct_1(k1_partfun1(A_128, B_125, C_124, D_126, E_127, F_129)) | ~m1_subset_1(F_129, k1_zfmisc_1(k2_zfmisc_1(C_124, D_126))) | ~v1_funct_1(F_129) | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_128, B_125))) | ~v1_funct_1(E_127))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.22/2.67  tff(c_560, plain, (![A_128, B_125, E_127]: (v1_funct_1(k1_partfun1(A_128, B_125, '#skF_2', '#skF_1', E_127, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_128, B_125))) | ~v1_funct_1(E_127))), inference(resolution, [status(thm)], [c_62, c_554])).
% 7.22/2.67  tff(c_585, plain, (![A_133, B_134, E_135]: (v1_funct_1(k1_partfun1(A_133, B_134, '#skF_2', '#skF_1', E_135, '#skF_4')) | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))) | ~v1_funct_1(E_135))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_560])).
% 7.22/2.67  tff(c_591, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_585])).
% 7.22/2.67  tff(c_598, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_507, c_591])).
% 7.22/2.67  tff(c_8, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.22/2.67  tff(c_77, plain, (![A_6]: (k2_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_8])).
% 7.22/2.67  tff(c_10, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.22/2.67  tff(c_76, plain, (![A_7]: (v1_relat_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_10])).
% 7.22/2.67  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.22/2.67  tff(c_114, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.22/2.67  tff(c_120, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_114])).
% 7.22/2.67  tff(c_129, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_120])).
% 7.22/2.67  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.22/2.67  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.22/2.67  tff(c_143, plain, (![A_61, B_62, C_63]: (k2_relset_1(A_61, B_62, C_63)=k2_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.22/2.67  tff(c_149, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_143])).
% 7.22/2.67  tff(c_156, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_149])).
% 7.22/2.67  tff(c_18, plain, (![A_9, B_11]: (k2_funct_1(A_9)=B_11 | k6_relat_1(k2_relat_1(A_9))!=k5_relat_1(B_11, A_9) | k2_relat_1(B_11)!=k1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.22/2.67  tff(c_516, plain, (![A_120, B_121]: (k2_funct_1(A_120)=B_121 | k6_partfun1(k2_relat_1(A_120))!=k5_relat_1(B_121, A_120) | k2_relat_1(B_121)!=k1_relat_1(A_120) | ~v2_funct_1(A_120) | ~v1_funct_1(B_121) | ~v1_relat_1(B_121) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_18])).
% 7.22/2.67  tff(c_520, plain, (![B_121]: (k2_funct_1('#skF_3')=B_121 | k5_relat_1(B_121, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_121)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_121) | ~v1_relat_1(B_121) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_156, c_516])).
% 7.22/2.67  tff(c_527, plain, (![B_122]: (k2_funct_1('#skF_3')=B_122 | k5_relat_1(B_122, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_122)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_122) | ~v1_relat_1(B_122))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_72, c_56, c_520])).
% 7.22/2.67  tff(c_539, plain, (![A_7]: (k6_partfun1(A_7)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_7), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_7))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_7)))), inference(resolution, [status(thm)], [c_76, c_527])).
% 7.22/2.67  tff(c_549, plain, (![A_7]: (k6_partfun1(A_7)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_7), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_7 | ~v1_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_539])).
% 7.22/2.67  tff(c_605, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_598, c_549])).
% 7.22/2.67  tff(c_608, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_605])).
% 7.22/2.67  tff(c_6, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.22/2.67  tff(c_78, plain, (![A_6]: (k1_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6])).
% 7.22/2.67  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.22/2.67  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.22/2.67  tff(c_679, plain, (![A_151, C_152, B_153]: (k6_partfun1(A_151)=k5_relat_1(C_152, k2_funct_1(C_152)) | k1_xboole_0=B_153 | ~v2_funct_1(C_152) | k2_relset_1(A_151, B_153, C_152)!=B_153 | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_151, B_153))) | ~v1_funct_2(C_152, A_151, B_153) | ~v1_funct_1(C_152))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.22/2.67  tff(c_683, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_679])).
% 7.22/2.67  tff(c_691, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_683])).
% 7.22/2.67  tff(c_692, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_691])).
% 7.22/2.67  tff(c_16, plain, (![A_8]: (k1_relat_1(k5_relat_1(A_8, k2_funct_1(A_8)))=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.22/2.67  tff(c_700, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_692, c_16])).
% 7.22/2.67  tff(c_707, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_72, c_56, c_78, c_700])).
% 7.22/2.67  tff(c_709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_608, c_707])).
% 7.22/2.67  tff(c_711, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_605])).
% 7.22/2.67  tff(c_50, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.22/2.67  tff(c_123, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_114])).
% 7.22/2.67  tff(c_132, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_123])).
% 7.22/2.67  tff(c_530, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_132, c_527])).
% 7.22/2.67  tff(c_542, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_530])).
% 7.22/2.67  tff(c_543, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_542])).
% 7.22/2.67  tff(c_550, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_543])).
% 7.22/2.67  tff(c_714, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_711, c_550])).
% 7.22/2.67  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.22/2.67  tff(c_133, plain, (![A_58, B_59, D_60]: (r2_relset_1(A_58, B_59, D_60, D_60) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.22/2.67  tff(c_140, plain, (![A_19]: (r2_relset_1(A_19, A_19, k6_partfun1(A_19), k6_partfun1(A_19)))), inference(resolution, [status(thm)], [c_73, c_133])).
% 7.22/2.67  tff(c_157, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_143])).
% 7.22/2.67  tff(c_1469, plain, (![A_216, B_217, C_218, D_219]: (k2_relset_1(A_216, B_217, C_218)=B_217 | ~r2_relset_1(B_217, B_217, k1_partfun1(B_217, A_216, A_216, B_217, D_219, C_218), k6_partfun1(B_217)) | ~m1_subset_1(D_219, k1_zfmisc_1(k2_zfmisc_1(B_217, A_216))) | ~v1_funct_2(D_219, B_217, A_216) | ~v1_funct_1(D_219) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))) | ~v1_funct_2(C_218, A_216, B_217) | ~v1_funct_1(C_218))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.22/2.67  tff(c_1475, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_507, c_1469])).
% 7.22/2.67  tff(c_1479, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_140, c_157, c_1475])).
% 7.22/2.67  tff(c_1481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_714, c_1479])).
% 7.22/2.67  tff(c_1482, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_543])).
% 7.22/2.67  tff(c_2436, plain, (![E_330, C_329, F_328, D_325, A_327, B_326]: (k1_partfun1(A_327, B_326, C_329, D_325, E_330, F_328)=k5_relat_1(E_330, F_328) | ~m1_subset_1(F_328, k1_zfmisc_1(k2_zfmisc_1(C_329, D_325))) | ~v1_funct_1(F_328) | ~m1_subset_1(E_330, k1_zfmisc_1(k2_zfmisc_1(A_327, B_326))) | ~v1_funct_1(E_330))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.22/2.67  tff(c_2442, plain, (![A_327, B_326, E_330]: (k1_partfun1(A_327, B_326, '#skF_2', '#skF_1', E_330, '#skF_4')=k5_relat_1(E_330, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_330, k1_zfmisc_1(k2_zfmisc_1(A_327, B_326))) | ~v1_funct_1(E_330))), inference(resolution, [status(thm)], [c_62, c_2436])).
% 7.22/2.67  tff(c_2679, plain, (![A_352, B_353, E_354]: (k1_partfun1(A_352, B_353, '#skF_2', '#skF_1', E_354, '#skF_4')=k5_relat_1(E_354, '#skF_4') | ~m1_subset_1(E_354, k1_zfmisc_1(k2_zfmisc_1(A_352, B_353))) | ~v1_funct_1(E_354))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2442])).
% 7.22/2.67  tff(c_2685, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2679])).
% 7.22/2.67  tff(c_2692, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_507, c_2685])).
% 7.22/2.67  tff(c_1483, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_543])).
% 7.22/2.67  tff(c_74, plain, (![A_9, B_11]: (k2_funct_1(A_9)=B_11 | k6_partfun1(k2_relat_1(A_9))!=k5_relat_1(B_11, A_9) | k2_relat_1(B_11)!=k1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_18])).
% 7.22/2.67  tff(c_1487, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_11, '#skF_4') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1483, c_74])).
% 7.22/2.67  tff(c_1491, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_11, '#skF_4') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_66, c_1487])).
% 7.22/2.67  tff(c_1499, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1491])).
% 7.22/2.67  tff(c_54, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.22/2.67  tff(c_12, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.22/2.67  tff(c_75, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_12])).
% 7.22/2.67  tff(c_2382, plain, (![E_309, D_308, B_306, C_307, A_305]: (k1_xboole_0=C_307 | v2_funct_1(E_309) | k2_relset_1(A_305, B_306, D_308)!=B_306 | ~v2_funct_1(k1_partfun1(A_305, B_306, B_306, C_307, D_308, E_309)) | ~m1_subset_1(E_309, k1_zfmisc_1(k2_zfmisc_1(B_306, C_307))) | ~v1_funct_2(E_309, B_306, C_307) | ~v1_funct_1(E_309) | ~m1_subset_1(D_308, k1_zfmisc_1(k2_zfmisc_1(A_305, B_306))) | ~v1_funct_2(D_308, A_305, B_306) | ~v1_funct_1(D_308))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.22/2.67  tff(c_2388, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_507, c_2382])).
% 7.22/2.67  tff(c_2396, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_64, c_62, c_75, c_60, c_2388])).
% 7.22/2.67  tff(c_2398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1499, c_54, c_2396])).
% 7.22/2.67  tff(c_2400, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1491])).
% 7.22/2.67  tff(c_1484, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1483, c_157])).
% 7.22/2.67  tff(c_2499, plain, (![B_338, C_339, A_340]: (k6_partfun1(B_338)=k5_relat_1(k2_funct_1(C_339), C_339) | k1_xboole_0=B_338 | ~v2_funct_1(C_339) | k2_relset_1(A_340, B_338, C_339)!=B_338 | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(A_340, B_338))) | ~v1_funct_2(C_339, A_340, B_338) | ~v1_funct_1(C_339))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.22/2.67  tff(c_2505, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_2499])).
% 7.22/2.67  tff(c_2515, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1484, c_2400, c_2505])).
% 7.22/2.67  tff(c_2516, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_54, c_2515])).
% 7.22/2.67  tff(c_2526, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2516])).
% 7.22/2.67  tff(c_2557, plain, (![A_345, C_346, B_347]: (k6_partfun1(A_345)=k5_relat_1(C_346, k2_funct_1(C_346)) | k1_xboole_0=B_347 | ~v2_funct_1(C_346) | k2_relset_1(A_345, B_347, C_346)!=B_347 | ~m1_subset_1(C_346, k1_zfmisc_1(k2_zfmisc_1(A_345, B_347))) | ~v1_funct_2(C_346, A_345, B_347) | ~v1_funct_1(C_346))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.22/2.67  tff(c_2561, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2557])).
% 7.22/2.67  tff(c_2569, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_2561])).
% 7.22/2.67  tff(c_2570, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_2569])).
% 7.22/2.67  tff(c_2578, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2570, c_16])).
% 7.22/2.67  tff(c_2585, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_72, c_56, c_78, c_2578])).
% 7.22/2.67  tff(c_2587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2526, c_2585])).
% 7.22/2.67  tff(c_2589, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2516])).
% 7.22/2.67  tff(c_2594, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2589, c_1484])).
% 7.22/2.67  tff(c_2629, plain, (![A_349, C_350, B_351]: (k6_partfun1(A_349)=k5_relat_1(C_350, k2_funct_1(C_350)) | k1_xboole_0=B_351 | ~v2_funct_1(C_350) | k2_relset_1(A_349, B_351, C_350)!=B_351 | ~m1_subset_1(C_350, k1_zfmisc_1(k2_zfmisc_1(A_349, B_351))) | ~v1_funct_2(C_350, A_349, B_351) | ~v1_funct_1(C_350))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.22/2.67  tff(c_2635, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_2629])).
% 7.22/2.67  tff(c_2645, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_2594, c_2400, c_2635])).
% 7.22/2.67  tff(c_2646, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_2645])).
% 7.22/2.67  tff(c_2664, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2646, c_16])).
% 7.22/2.67  tff(c_2671, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_66, c_2400, c_78, c_2664])).
% 7.22/2.67  tff(c_2399, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_11, '#skF_4') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(splitRight, [status(thm)], [c_1491])).
% 7.22/2.67  tff(c_2591, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k5_relat_1(B_11, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_2589, c_2399])).
% 7.22/2.67  tff(c_4728, plain, (![B_451]: (k2_funct_1('#skF_4')=B_451 | k5_relat_1(B_451, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_451)!='#skF_2' | ~v1_funct_1(B_451) | ~v1_relat_1(B_451))), inference(demodulation, [status(thm), theory('equality')], [c_2671, c_2591])).
% 7.22/2.67  tff(c_4821, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_129, c_4728])).
% 7.22/2.67  tff(c_4916, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_156, c_2692, c_4821])).
% 7.22/2.67  tff(c_4921, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4916, c_2646])).
% 7.22/2.67  tff(c_4924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1482, c_4921])).
% 7.22/2.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.22/2.67  
% 7.22/2.67  Inference rules
% 7.22/2.67  ----------------------
% 7.22/2.67  #Ref     : 0
% 7.22/2.67  #Sup     : 995
% 7.22/2.67  #Fact    : 0
% 7.22/2.67  #Define  : 0
% 7.22/2.67  #Split   : 29
% 7.22/2.67  #Chain   : 0
% 7.22/2.67  #Close   : 0
% 7.22/2.67  
% 7.22/2.67  Ordering : KBO
% 7.22/2.67  
% 7.22/2.67  Simplification rules
% 7.22/2.67  ----------------------
% 7.22/2.67  #Subsume      : 43
% 7.22/2.67  #Demod        : 1423
% 7.22/2.67  #Tautology    : 259
% 7.22/2.67  #SimpNegUnit  : 93
% 7.22/2.67  #BackRed      : 50
% 7.22/2.67  
% 7.22/2.67  #Partial instantiations: 0
% 7.22/2.67  #Strategies tried      : 1
% 7.22/2.67  
% 7.22/2.67  Timing (in seconds)
% 7.22/2.67  ----------------------
% 7.22/2.67  Preprocessing        : 0.38
% 7.22/2.67  Parsing              : 0.20
% 7.22/2.68  CNF conversion       : 0.03
% 7.22/2.68  Main loop            : 1.50
% 7.22/2.68  Inferencing          : 0.47
% 7.22/2.68  Reduction            : 0.62
% 7.22/2.68  Demodulation         : 0.47
% 7.22/2.68  BG Simplification    : 0.05
% 7.22/2.68  Subsumption          : 0.26
% 7.22/2.68  Abstraction          : 0.07
% 7.22/2.68  MUC search           : 0.00
% 7.22/2.68  Cooper               : 0.00
% 7.22/2.68  Total                : 1.94
% 7.22/2.68  Index Insertion      : 0.00
% 7.22/2.68  Index Deletion       : 0.00
% 7.22/2.68  Index Matching       : 0.00
% 7.22/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
