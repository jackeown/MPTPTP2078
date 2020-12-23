%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:24 EST 2020

% Result     : Theorem 7.21s
% Output     : CNFRefutation 7.40s
% Verified   : 
% Statistics : Number of formulae       :  167 (1193 expanded)
%              Number of leaves         :   41 ( 434 expanded)
%              Depth                    :   21
%              Number of atoms          :  423 (4877 expanded)
%              Number of equality atoms :  157 (1665 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_194,negated_conjecture,(
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

tff(f_107,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_109,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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

tff(f_168,axiom,(
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

tff(f_126,axiom,(
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

tff(f_152,axiom,(
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

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_326,plain,(
    ! [C_103,E_104,D_99,F_102,A_101,B_100] :
      ( k1_partfun1(A_101,B_100,C_103,D_99,E_104,F_102) = k5_relat_1(E_104,F_102)
      | ~ m1_subset_1(F_102,k1_zfmisc_1(k2_zfmisc_1(C_103,D_99)))
      | ~ v1_funct_1(F_102)
      | ~ m1_subset_1(E_104,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100)))
      | ~ v1_funct_1(E_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_330,plain,(
    ! [A_101,B_100,E_104] :
      ( k1_partfun1(A_101,B_100,'#skF_2','#skF_1',E_104,'#skF_4') = k5_relat_1(E_104,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_104,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100)))
      | ~ v1_funct_1(E_104) ) ),
    inference(resolution,[status(thm)],[c_64,c_326])).

tff(c_399,plain,(
    ! [A_116,B_117,E_118] :
      ( k1_partfun1(A_116,B_117,'#skF_2','#skF_1',E_118,'#skF_4') = k5_relat_1(E_118,'#skF_4')
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_1(E_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_330])).

tff(c_408,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_399])).

tff(c_415,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_408])).

tff(c_32,plain,(
    ! [A_25] : m1_subset_1(k6_partfun1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_196,plain,(
    ! [D_69,C_70,A_71,B_72] :
      ( D_69 = C_70
      | ~ r2_relset_1(A_71,B_72,C_70,D_69)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_204,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_196])).

tff(c_219,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_204])).

tff(c_220,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_422,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_220])).

tff(c_501,plain,(
    ! [D_130,F_129,C_125,E_126,A_128,B_127] :
      ( m1_subset_1(k1_partfun1(A_128,B_127,C_125,D_130,E_126,F_129),k1_zfmisc_1(k2_zfmisc_1(A_128,D_130)))
      | ~ m1_subset_1(F_129,k1_zfmisc_1(k2_zfmisc_1(C_125,D_130)))
      | ~ v1_funct_1(F_129)
      | ~ m1_subset_1(E_126,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127)))
      | ~ v1_funct_1(E_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_534,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_501])).

tff(c_559,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_534])).

tff(c_561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_422,c_559])).

tff(c_562,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_609,plain,(
    ! [B_137,A_138,F_139,E_136,D_140,C_135] :
      ( v1_funct_1(k1_partfun1(A_138,B_137,C_135,D_140,E_136,F_139))
      | ~ m1_subset_1(F_139,k1_zfmisc_1(k2_zfmisc_1(C_135,D_140)))
      | ~ v1_funct_1(F_139)
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_1(E_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_613,plain,(
    ! [A_138,B_137,E_136] :
      ( v1_funct_1(k1_partfun1(A_138,B_137,'#skF_2','#skF_1',E_136,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_1(E_136) ) ),
    inference(resolution,[status(thm)],[c_64,c_609])).

tff(c_623,plain,(
    ! [A_141,B_142,E_143] :
      ( v1_funct_1(k1_partfun1(A_141,B_142,'#skF_2','#skF_1',E_143,'#skF_4'))
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ v1_funct_1(E_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_613])).

tff(c_632,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_623])).

tff(c_639,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_562,c_632])).

tff(c_36,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_8,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_78,plain,(
    ! [A_6] : k2_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8])).

tff(c_10,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_77,plain,(
    ! [A_7] : v1_relat_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_10])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_116,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_125,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_116])).

tff(c_134,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_125])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_145,plain,(
    ! [A_62,B_63,C_64] :
      ( k2_relset_1(A_62,B_63,C_64) = k2_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_154,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_145])).

tff(c_159,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_154])).

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

tff(c_571,plain,(
    ! [A_131,B_132] :
      ( k2_funct_1(A_131) = B_132
      | k6_partfun1(k2_relat_1(A_131)) != k5_relat_1(B_132,A_131)
      | k2_relat_1(B_132) != k1_relat_1(A_131)
      | ~ v2_funct_1(A_131)
      | ~ v1_funct_1(B_132)
      | ~ v1_relat_1(B_132)
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_18])).

tff(c_575,plain,(
    ! [B_132] :
      ( k2_funct_1('#skF_3') = B_132
      | k5_relat_1(B_132,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_132) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_132)
      | ~ v1_relat_1(B_132)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_571])).

tff(c_582,plain,(
    ! [B_133] :
      ( k2_funct_1('#skF_3') = B_133
      | k5_relat_1(B_133,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_133) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_133)
      | ~ v1_relat_1(B_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_74,c_58,c_575])).

tff(c_594,plain,(
    ! [A_7] :
      ( k6_partfun1(A_7) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_7),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_7)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_77,c_582])).

tff(c_604,plain,(
    ! [A_7] :
      ( k6_partfun1(A_7) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_7),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_7
      | ~ v1_funct_1(k6_partfun1(A_7)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_594])).

tff(c_643,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_639,c_604])).

tff(c_663,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_643])).

tff(c_6,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_79,plain,(
    ! [A_6] : k1_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_718,plain,(
    ! [A_159,C_160,B_161] :
      ( k6_partfun1(A_159) = k5_relat_1(C_160,k2_funct_1(C_160))
      | k1_xboole_0 = B_161
      | ~ v2_funct_1(C_160)
      | k2_relset_1(A_159,B_161,C_160) != B_161
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_159,B_161)))
      | ~ v1_funct_2(C_160,A_159,B_161)
      | ~ v1_funct_1(C_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_724,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_718])).

tff(c_734,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_62,c_58,c_724])).

tff(c_735,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_734])).

tff(c_16,plain,(
    ! [A_8] :
      ( k1_relat_1(k5_relat_1(A_8,k2_funct_1(A_8))) = k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_739,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_735,c_16])).

tff(c_746,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_74,c_58,c_79,c_739])).

tff(c_748,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_663,c_746])).

tff(c_750,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_643])).

tff(c_52,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_122,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_116])).

tff(c_131,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_122])).

tff(c_588,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_131,c_582])).

tff(c_600,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_588])).

tff(c_601,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_600])).

tff(c_605,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_601])).

tff(c_753,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_750,c_605])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_135,plain,(
    ! [A_59,B_60,D_61] :
      ( r2_relset_1(A_59,B_60,D_61,D_61)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_142,plain,(
    ! [A_25] : r2_relset_1(A_25,A_25,k6_partfun1(A_25),k6_partfun1(A_25)) ),
    inference(resolution,[status(thm)],[c_32,c_135])).

tff(c_157,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_145])).

tff(c_1646,plain,(
    ! [A_229,B_230,C_231,D_232] :
      ( k2_relset_1(A_229,B_230,C_231) = B_230
      | ~ r2_relset_1(B_230,B_230,k1_partfun1(B_230,A_229,A_229,B_230,D_232,C_231),k6_partfun1(B_230))
      | ~ m1_subset_1(D_232,k1_zfmisc_1(k2_zfmisc_1(B_230,A_229)))
      | ~ v1_funct_2(D_232,B_230,A_229)
      | ~ v1_funct_1(D_232)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230)))
      | ~ v1_funct_2(C_231,A_229,B_230)
      | ~ v1_funct_1(C_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1652,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_1646])).

tff(c_1656,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_74,c_72,c_70,c_142,c_157,c_1652])).

tff(c_1658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_753,c_1656])).

tff(c_1659,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_601])).

tff(c_2676,plain,(
    ! [D_346,A_348,C_350,E_351,B_347,F_349] :
      ( k1_partfun1(A_348,B_347,C_350,D_346,E_351,F_349) = k5_relat_1(E_351,F_349)
      | ~ m1_subset_1(F_349,k1_zfmisc_1(k2_zfmisc_1(C_350,D_346)))
      | ~ v1_funct_1(F_349)
      | ~ m1_subset_1(E_351,k1_zfmisc_1(k2_zfmisc_1(A_348,B_347)))
      | ~ v1_funct_1(E_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2680,plain,(
    ! [A_348,B_347,E_351] :
      ( k1_partfun1(A_348,B_347,'#skF_2','#skF_1',E_351,'#skF_4') = k5_relat_1(E_351,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_351,k1_zfmisc_1(k2_zfmisc_1(A_348,B_347)))
      | ~ v1_funct_1(E_351) ) ),
    inference(resolution,[status(thm)],[c_64,c_2676])).

tff(c_2912,plain,(
    ! [A_375,B_376,E_377] :
      ( k1_partfun1(A_375,B_376,'#skF_2','#skF_1',E_377,'#skF_4') = k5_relat_1(E_377,'#skF_4')
      | ~ m1_subset_1(E_377,k1_zfmisc_1(k2_zfmisc_1(A_375,B_376)))
      | ~ v1_funct_1(E_377) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2680])).

tff(c_2921,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_2912])).

tff(c_2928,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_562,c_2921])).

tff(c_1660,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_601])).

tff(c_75,plain,(
    ! [A_9,B_11] :
      ( k2_funct_1(A_9) = B_11
      | k6_partfun1(k2_relat_1(A_9)) != k5_relat_1(B_11,A_9)
      | k2_relat_1(B_11) != k1_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_18])).

tff(c_1664,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_11,'#skF_4')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1660,c_75])).

tff(c_1668,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_11,'#skF_4')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_68,c_1664])).

tff(c_1676,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1668])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_12,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_12])).

tff(c_2618,plain,(
    ! [A_326,B_327,E_330,C_328,D_329] :
      ( k1_xboole_0 = C_328
      | v2_funct_1(E_330)
      | k2_relset_1(A_326,B_327,D_329) != B_327
      | ~ v2_funct_1(k1_partfun1(A_326,B_327,B_327,C_328,D_329,E_330))
      | ~ m1_subset_1(E_330,k1_zfmisc_1(k2_zfmisc_1(B_327,C_328)))
      | ~ v1_funct_2(E_330,B_327,C_328)
      | ~ v1_funct_1(E_330)
      | ~ m1_subset_1(D_329,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327)))
      | ~ v1_funct_2(D_329,A_326,B_327)
      | ~ v1_funct_1(D_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2624,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_562,c_2618])).

tff(c_2632,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_64,c_76,c_62,c_2624])).

tff(c_2634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1676,c_56,c_2632])).

tff(c_2636,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1668])).

tff(c_2640,plain,(
    ! [B_338,F_340,A_339,D_341,E_337,C_336] :
      ( v1_funct_1(k1_partfun1(A_339,B_338,C_336,D_341,E_337,F_340))
      | ~ m1_subset_1(F_340,k1_zfmisc_1(k2_zfmisc_1(C_336,D_341)))
      | ~ v1_funct_1(F_340)
      | ~ m1_subset_1(E_337,k1_zfmisc_1(k2_zfmisc_1(A_339,B_338)))
      | ~ v1_funct_1(E_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2644,plain,(
    ! [A_339,B_338,E_337] :
      ( v1_funct_1(k1_partfun1(A_339,B_338,'#skF_2','#skF_1',E_337,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_337,k1_zfmisc_1(k2_zfmisc_1(A_339,B_338)))
      | ~ v1_funct_1(E_337) ) ),
    inference(resolution,[status(thm)],[c_64,c_2640])).

tff(c_2654,plain,(
    ! [A_342,B_343,E_344] :
      ( v1_funct_1(k1_partfun1(A_342,B_343,'#skF_2','#skF_1',E_344,'#skF_4'))
      | ~ m1_subset_1(E_344,k1_zfmisc_1(k2_zfmisc_1(A_342,B_343)))
      | ~ v1_funct_1(E_344) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2644])).

tff(c_2663,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_2654])).

tff(c_2670,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_562,c_2663])).

tff(c_2674,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_2670,c_604])).

tff(c_2690,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2674])).

tff(c_2802,plain,(
    ! [A_366,C_367,B_368] :
      ( k6_partfun1(A_366) = k5_relat_1(C_367,k2_funct_1(C_367))
      | k1_xboole_0 = B_368
      | ~ v2_funct_1(C_367)
      | k2_relset_1(A_366,B_368,C_367) != B_368
      | ~ m1_subset_1(C_367,k1_zfmisc_1(k2_zfmisc_1(A_366,B_368)))
      | ~ v1_funct_2(C_367,A_366,B_368)
      | ~ v1_funct_1(C_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_2808,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_2802])).

tff(c_2818,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_62,c_58,c_2808])).

tff(c_2819,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2818])).

tff(c_2823,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2819,c_16])).

tff(c_2830,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_74,c_58,c_79,c_2823])).

tff(c_2832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2690,c_2830])).

tff(c_2834,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2674])).

tff(c_1661,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1660,c_157])).

tff(c_2839,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2834,c_1661])).

tff(c_2939,plain,(
    ! [A_379,C_380,B_381] :
      ( k6_partfun1(A_379) = k5_relat_1(C_380,k2_funct_1(C_380))
      | k1_xboole_0 = B_381
      | ~ v2_funct_1(C_380)
      | k2_relset_1(A_379,B_381,C_380) != B_381
      | ~ m1_subset_1(C_380,k1_zfmisc_1(k2_zfmisc_1(A_379,B_381)))
      | ~ v1_funct_2(C_380,A_379,B_381)
      | ~ v1_funct_1(C_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_2943,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_2939])).

tff(c_2951,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2839,c_2636,c_2943])).

tff(c_2952,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2951])).

tff(c_2974,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2952,c_16])).

tff(c_2981,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_68,c_2636,c_79,c_2974])).

tff(c_2635,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_11,'#skF_4')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(splitRight,[status(thm)],[c_1668])).

tff(c_2836,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k5_relat_1(B_11,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2834,c_2635])).

tff(c_5041,plain,(
    ! [B_482] :
      ( k2_funct_1('#skF_4') = B_482
      | k5_relat_1(B_482,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_482) != '#skF_2'
      | ~ v1_funct_1(B_482)
      | ~ v1_relat_1(B_482) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2981,c_2836])).

tff(c_5131,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_134,c_5041])).

tff(c_5226,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_159,c_2928,c_5131])).

tff(c_5234,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5226,c_2952])).

tff(c_5237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1659,c_5234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.21/2.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/2.59  
% 7.21/2.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/2.59  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.21/2.59  
% 7.21/2.59  %Foreground sorts:
% 7.21/2.59  
% 7.21/2.59  
% 7.21/2.59  %Background operators:
% 7.21/2.59  
% 7.21/2.59  
% 7.21/2.59  %Foreground operators:
% 7.21/2.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.21/2.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.21/2.59  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.21/2.59  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.21/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.21/2.59  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.21/2.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.21/2.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.21/2.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.21/2.59  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.21/2.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.21/2.59  tff('#skF_2', type, '#skF_2': $i).
% 7.21/2.59  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.21/2.59  tff('#skF_3', type, '#skF_3': $i).
% 7.21/2.59  tff('#skF_1', type, '#skF_1': $i).
% 7.21/2.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.21/2.59  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.21/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.21/2.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.21/2.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.21/2.59  tff('#skF_4', type, '#skF_4': $i).
% 7.21/2.59  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.21/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.21/2.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.21/2.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.21/2.59  
% 7.40/2.62  tff(f_194, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 7.40/2.62  tff(f_107, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.40/2.62  tff(f_97, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.40/2.62  tff(f_81, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.40/2.62  tff(f_93, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.40/2.62  tff(f_109, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.40/2.62  tff(f_38, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.40/2.62  tff(f_42, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.40/2.62  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.40/2.62  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.40/2.62  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.40/2.62  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 7.40/2.62  tff(f_168, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 7.40/2.62  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 7.40/2.62  tff(f_126, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.40/2.62  tff(f_152, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 7.40/2.62  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.40/2.62  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.40/2.62  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.40/2.62  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.40/2.62  tff(c_326, plain, (![C_103, E_104, D_99, F_102, A_101, B_100]: (k1_partfun1(A_101, B_100, C_103, D_99, E_104, F_102)=k5_relat_1(E_104, F_102) | ~m1_subset_1(F_102, k1_zfmisc_1(k2_zfmisc_1(C_103, D_99))) | ~v1_funct_1(F_102) | ~m1_subset_1(E_104, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))) | ~v1_funct_1(E_104))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.40/2.62  tff(c_330, plain, (![A_101, B_100, E_104]: (k1_partfun1(A_101, B_100, '#skF_2', '#skF_1', E_104, '#skF_4')=k5_relat_1(E_104, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_104, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))) | ~v1_funct_1(E_104))), inference(resolution, [status(thm)], [c_64, c_326])).
% 7.40/2.62  tff(c_399, plain, (![A_116, B_117, E_118]: (k1_partfun1(A_116, B_117, '#skF_2', '#skF_1', E_118, '#skF_4')=k5_relat_1(E_118, '#skF_4') | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_1(E_118))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_330])).
% 7.40/2.62  tff(c_408, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_399])).
% 7.40/2.62  tff(c_415, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_408])).
% 7.40/2.62  tff(c_32, plain, (![A_25]: (m1_subset_1(k6_partfun1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.40/2.62  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.40/2.62  tff(c_196, plain, (![D_69, C_70, A_71, B_72]: (D_69=C_70 | ~r2_relset_1(A_71, B_72, C_70, D_69) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.40/2.62  tff(c_204, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_196])).
% 7.40/2.62  tff(c_219, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_204])).
% 7.40/2.62  tff(c_220, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_219])).
% 7.40/2.62  tff(c_422, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_415, c_220])).
% 7.40/2.62  tff(c_501, plain, (![D_130, F_129, C_125, E_126, A_128, B_127]: (m1_subset_1(k1_partfun1(A_128, B_127, C_125, D_130, E_126, F_129), k1_zfmisc_1(k2_zfmisc_1(A_128, D_130))) | ~m1_subset_1(F_129, k1_zfmisc_1(k2_zfmisc_1(C_125, D_130))) | ~v1_funct_1(F_129) | ~m1_subset_1(E_126, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))) | ~v1_funct_1(E_126))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.40/2.62  tff(c_534, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_415, c_501])).
% 7.40/2.62  tff(c_559, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_534])).
% 7.40/2.62  tff(c_561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_422, c_559])).
% 7.40/2.62  tff(c_562, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_219])).
% 7.40/2.62  tff(c_609, plain, (![B_137, A_138, F_139, E_136, D_140, C_135]: (v1_funct_1(k1_partfun1(A_138, B_137, C_135, D_140, E_136, F_139)) | ~m1_subset_1(F_139, k1_zfmisc_1(k2_zfmisc_1(C_135, D_140))) | ~v1_funct_1(F_139) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_1(E_136))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.40/2.62  tff(c_613, plain, (![A_138, B_137, E_136]: (v1_funct_1(k1_partfun1(A_138, B_137, '#skF_2', '#skF_1', E_136, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_1(E_136))), inference(resolution, [status(thm)], [c_64, c_609])).
% 7.40/2.62  tff(c_623, plain, (![A_141, B_142, E_143]: (v1_funct_1(k1_partfun1(A_141, B_142, '#skF_2', '#skF_1', E_143, '#skF_4')) | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~v1_funct_1(E_143))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_613])).
% 7.40/2.62  tff(c_632, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_623])).
% 7.40/2.62  tff(c_639, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_562, c_632])).
% 7.40/2.62  tff(c_36, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.40/2.62  tff(c_8, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.40/2.62  tff(c_78, plain, (![A_6]: (k2_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8])).
% 7.40/2.62  tff(c_10, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.40/2.62  tff(c_77, plain, (![A_7]: (v1_relat_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_10])).
% 7.40/2.62  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.40/2.62  tff(c_116, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.40/2.62  tff(c_125, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_116])).
% 7.40/2.62  tff(c_134, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_125])).
% 7.40/2.62  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.40/2.62  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.40/2.62  tff(c_145, plain, (![A_62, B_63, C_64]: (k2_relset_1(A_62, B_63, C_64)=k2_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.40/2.62  tff(c_154, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_145])).
% 7.40/2.62  tff(c_159, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_154])).
% 7.40/2.62  tff(c_18, plain, (![A_9, B_11]: (k2_funct_1(A_9)=B_11 | k6_relat_1(k2_relat_1(A_9))!=k5_relat_1(B_11, A_9) | k2_relat_1(B_11)!=k1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.40/2.62  tff(c_571, plain, (![A_131, B_132]: (k2_funct_1(A_131)=B_132 | k6_partfun1(k2_relat_1(A_131))!=k5_relat_1(B_132, A_131) | k2_relat_1(B_132)!=k1_relat_1(A_131) | ~v2_funct_1(A_131) | ~v1_funct_1(B_132) | ~v1_relat_1(B_132) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_18])).
% 7.40/2.62  tff(c_575, plain, (![B_132]: (k2_funct_1('#skF_3')=B_132 | k5_relat_1(B_132, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_132)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_132) | ~v1_relat_1(B_132) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_159, c_571])).
% 7.40/2.62  tff(c_582, plain, (![B_133]: (k2_funct_1('#skF_3')=B_133 | k5_relat_1(B_133, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_133)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_133) | ~v1_relat_1(B_133))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_74, c_58, c_575])).
% 7.40/2.62  tff(c_594, plain, (![A_7]: (k6_partfun1(A_7)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_7), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_7))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_7)))), inference(resolution, [status(thm)], [c_77, c_582])).
% 7.40/2.62  tff(c_604, plain, (![A_7]: (k6_partfun1(A_7)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_7), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_7 | ~v1_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_594])).
% 7.40/2.62  tff(c_643, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_639, c_604])).
% 7.40/2.62  tff(c_663, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_643])).
% 7.40/2.62  tff(c_6, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.40/2.62  tff(c_79, plain, (![A_6]: (k1_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6])).
% 7.40/2.62  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.40/2.62  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.40/2.62  tff(c_718, plain, (![A_159, C_160, B_161]: (k6_partfun1(A_159)=k5_relat_1(C_160, k2_funct_1(C_160)) | k1_xboole_0=B_161 | ~v2_funct_1(C_160) | k2_relset_1(A_159, B_161, C_160)!=B_161 | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_159, B_161))) | ~v1_funct_2(C_160, A_159, B_161) | ~v1_funct_1(C_160))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.40/2.62  tff(c_724, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_718])).
% 7.40/2.62  tff(c_734, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_62, c_58, c_724])).
% 7.40/2.62  tff(c_735, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_734])).
% 7.40/2.62  tff(c_16, plain, (![A_8]: (k1_relat_1(k5_relat_1(A_8, k2_funct_1(A_8)))=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.40/2.62  tff(c_739, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_735, c_16])).
% 7.40/2.62  tff(c_746, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_74, c_58, c_79, c_739])).
% 7.40/2.62  tff(c_748, plain, $false, inference(negUnitSimplification, [status(thm)], [c_663, c_746])).
% 7.40/2.62  tff(c_750, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_643])).
% 7.40/2.62  tff(c_52, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.40/2.62  tff(c_122, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_64, c_116])).
% 7.40/2.62  tff(c_131, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_122])).
% 7.40/2.62  tff(c_588, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_131, c_582])).
% 7.40/2.62  tff(c_600, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_588])).
% 7.40/2.62  tff(c_601, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_600])).
% 7.40/2.62  tff(c_605, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_601])).
% 7.40/2.62  tff(c_753, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_750, c_605])).
% 7.40/2.62  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.40/2.62  tff(c_135, plain, (![A_59, B_60, D_61]: (r2_relset_1(A_59, B_60, D_61, D_61) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.40/2.62  tff(c_142, plain, (![A_25]: (r2_relset_1(A_25, A_25, k6_partfun1(A_25), k6_partfun1(A_25)))), inference(resolution, [status(thm)], [c_32, c_135])).
% 7.40/2.62  tff(c_157, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_145])).
% 7.40/2.62  tff(c_1646, plain, (![A_229, B_230, C_231, D_232]: (k2_relset_1(A_229, B_230, C_231)=B_230 | ~r2_relset_1(B_230, B_230, k1_partfun1(B_230, A_229, A_229, B_230, D_232, C_231), k6_partfun1(B_230)) | ~m1_subset_1(D_232, k1_zfmisc_1(k2_zfmisc_1(B_230, A_229))) | ~v1_funct_2(D_232, B_230, A_229) | ~v1_funct_1(D_232) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))) | ~v1_funct_2(C_231, A_229, B_230) | ~v1_funct_1(C_231))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.40/2.62  tff(c_1652, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_562, c_1646])).
% 7.40/2.62  tff(c_1656, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_74, c_72, c_70, c_142, c_157, c_1652])).
% 7.40/2.62  tff(c_1658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_753, c_1656])).
% 7.40/2.62  tff(c_1659, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_601])).
% 7.40/2.62  tff(c_2676, plain, (![D_346, A_348, C_350, E_351, B_347, F_349]: (k1_partfun1(A_348, B_347, C_350, D_346, E_351, F_349)=k5_relat_1(E_351, F_349) | ~m1_subset_1(F_349, k1_zfmisc_1(k2_zfmisc_1(C_350, D_346))) | ~v1_funct_1(F_349) | ~m1_subset_1(E_351, k1_zfmisc_1(k2_zfmisc_1(A_348, B_347))) | ~v1_funct_1(E_351))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.40/2.62  tff(c_2680, plain, (![A_348, B_347, E_351]: (k1_partfun1(A_348, B_347, '#skF_2', '#skF_1', E_351, '#skF_4')=k5_relat_1(E_351, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_351, k1_zfmisc_1(k2_zfmisc_1(A_348, B_347))) | ~v1_funct_1(E_351))), inference(resolution, [status(thm)], [c_64, c_2676])).
% 7.40/2.62  tff(c_2912, plain, (![A_375, B_376, E_377]: (k1_partfun1(A_375, B_376, '#skF_2', '#skF_1', E_377, '#skF_4')=k5_relat_1(E_377, '#skF_4') | ~m1_subset_1(E_377, k1_zfmisc_1(k2_zfmisc_1(A_375, B_376))) | ~v1_funct_1(E_377))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2680])).
% 7.40/2.62  tff(c_2921, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_2912])).
% 7.40/2.62  tff(c_2928, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_562, c_2921])).
% 7.40/2.62  tff(c_1660, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_601])).
% 7.40/2.62  tff(c_75, plain, (![A_9, B_11]: (k2_funct_1(A_9)=B_11 | k6_partfun1(k2_relat_1(A_9))!=k5_relat_1(B_11, A_9) | k2_relat_1(B_11)!=k1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_18])).
% 7.40/2.62  tff(c_1664, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_11, '#skF_4') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1660, c_75])).
% 7.40/2.62  tff(c_1668, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_11, '#skF_4') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_68, c_1664])).
% 7.40/2.62  tff(c_1676, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1668])).
% 7.40/2.62  tff(c_56, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.40/2.62  tff(c_12, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.40/2.62  tff(c_76, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_12])).
% 7.40/2.62  tff(c_2618, plain, (![A_326, B_327, E_330, C_328, D_329]: (k1_xboole_0=C_328 | v2_funct_1(E_330) | k2_relset_1(A_326, B_327, D_329)!=B_327 | ~v2_funct_1(k1_partfun1(A_326, B_327, B_327, C_328, D_329, E_330)) | ~m1_subset_1(E_330, k1_zfmisc_1(k2_zfmisc_1(B_327, C_328))) | ~v1_funct_2(E_330, B_327, C_328) | ~v1_funct_1(E_330) | ~m1_subset_1(D_329, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))) | ~v1_funct_2(D_329, A_326, B_327) | ~v1_funct_1(D_329))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.40/2.62  tff(c_2624, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_562, c_2618])).
% 7.40/2.62  tff(c_2632, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_66, c_64, c_76, c_62, c_2624])).
% 7.40/2.62  tff(c_2634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1676, c_56, c_2632])).
% 7.40/2.62  tff(c_2636, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1668])).
% 7.40/2.62  tff(c_2640, plain, (![B_338, F_340, A_339, D_341, E_337, C_336]: (v1_funct_1(k1_partfun1(A_339, B_338, C_336, D_341, E_337, F_340)) | ~m1_subset_1(F_340, k1_zfmisc_1(k2_zfmisc_1(C_336, D_341))) | ~v1_funct_1(F_340) | ~m1_subset_1(E_337, k1_zfmisc_1(k2_zfmisc_1(A_339, B_338))) | ~v1_funct_1(E_337))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.40/2.62  tff(c_2644, plain, (![A_339, B_338, E_337]: (v1_funct_1(k1_partfun1(A_339, B_338, '#skF_2', '#skF_1', E_337, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_337, k1_zfmisc_1(k2_zfmisc_1(A_339, B_338))) | ~v1_funct_1(E_337))), inference(resolution, [status(thm)], [c_64, c_2640])).
% 7.40/2.62  tff(c_2654, plain, (![A_342, B_343, E_344]: (v1_funct_1(k1_partfun1(A_342, B_343, '#skF_2', '#skF_1', E_344, '#skF_4')) | ~m1_subset_1(E_344, k1_zfmisc_1(k2_zfmisc_1(A_342, B_343))) | ~v1_funct_1(E_344))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2644])).
% 7.40/2.62  tff(c_2663, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_2654])).
% 7.40/2.62  tff(c_2670, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_562, c_2663])).
% 7.40/2.62  tff(c_2674, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_2670, c_604])).
% 7.40/2.62  tff(c_2690, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2674])).
% 7.40/2.62  tff(c_2802, plain, (![A_366, C_367, B_368]: (k6_partfun1(A_366)=k5_relat_1(C_367, k2_funct_1(C_367)) | k1_xboole_0=B_368 | ~v2_funct_1(C_367) | k2_relset_1(A_366, B_368, C_367)!=B_368 | ~m1_subset_1(C_367, k1_zfmisc_1(k2_zfmisc_1(A_366, B_368))) | ~v1_funct_2(C_367, A_366, B_368) | ~v1_funct_1(C_367))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.40/2.62  tff(c_2808, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_2802])).
% 7.40/2.62  tff(c_2818, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_62, c_58, c_2808])).
% 7.40/2.62  tff(c_2819, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_2818])).
% 7.40/2.62  tff(c_2823, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2819, c_16])).
% 7.40/2.62  tff(c_2830, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_74, c_58, c_79, c_2823])).
% 7.40/2.62  tff(c_2832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2690, c_2830])).
% 7.40/2.62  tff(c_2834, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2674])).
% 7.40/2.62  tff(c_1661, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1660, c_157])).
% 7.40/2.62  tff(c_2839, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2834, c_1661])).
% 7.40/2.62  tff(c_2939, plain, (![A_379, C_380, B_381]: (k6_partfun1(A_379)=k5_relat_1(C_380, k2_funct_1(C_380)) | k1_xboole_0=B_381 | ~v2_funct_1(C_380) | k2_relset_1(A_379, B_381, C_380)!=B_381 | ~m1_subset_1(C_380, k1_zfmisc_1(k2_zfmisc_1(A_379, B_381))) | ~v1_funct_2(C_380, A_379, B_381) | ~v1_funct_1(C_380))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.40/2.62  tff(c_2943, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_2939])).
% 7.40/2.62  tff(c_2951, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_2839, c_2636, c_2943])).
% 7.40/2.62  tff(c_2952, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_2951])).
% 7.40/2.62  tff(c_2974, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2952, c_16])).
% 7.40/2.62  tff(c_2981, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_68, c_2636, c_79, c_2974])).
% 7.40/2.62  tff(c_2635, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_11, '#skF_4') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(splitRight, [status(thm)], [c_1668])).
% 7.40/2.62  tff(c_2836, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k5_relat_1(B_11, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_2834, c_2635])).
% 7.40/2.62  tff(c_5041, plain, (![B_482]: (k2_funct_1('#skF_4')=B_482 | k5_relat_1(B_482, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_482)!='#skF_2' | ~v1_funct_1(B_482) | ~v1_relat_1(B_482))), inference(demodulation, [status(thm), theory('equality')], [c_2981, c_2836])).
% 7.40/2.62  tff(c_5131, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_134, c_5041])).
% 7.40/2.62  tff(c_5226, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_159, c_2928, c_5131])).
% 7.40/2.62  tff(c_5234, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5226, c_2952])).
% 7.40/2.62  tff(c_5237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1659, c_5234])).
% 7.40/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.40/2.62  
% 7.40/2.62  Inference rules
% 7.40/2.62  ----------------------
% 7.40/2.62  #Ref     : 0
% 7.40/2.62  #Sup     : 1062
% 7.40/2.62  #Fact    : 0
% 7.40/2.62  #Define  : 0
% 7.40/2.62  #Split   : 28
% 7.40/2.62  #Chain   : 0
% 7.40/2.62  #Close   : 0
% 7.40/2.62  
% 7.40/2.62  Ordering : KBO
% 7.40/2.62  
% 7.40/2.62  Simplification rules
% 7.40/2.62  ----------------------
% 7.40/2.62  #Subsume      : 53
% 7.40/2.62  #Demod        : 1544
% 7.40/2.62  #Tautology    : 282
% 7.40/2.62  #SimpNegUnit  : 106
% 7.40/2.62  #BackRed      : 53
% 7.40/2.62  
% 7.40/2.62  #Partial instantiations: 0
% 7.40/2.62  #Strategies tried      : 1
% 7.40/2.62  
% 7.40/2.62  Timing (in seconds)
% 7.40/2.62  ----------------------
% 7.40/2.62  Preprocessing        : 0.39
% 7.40/2.62  Parsing              : 0.21
% 7.40/2.62  CNF conversion       : 0.02
% 7.40/2.62  Main loop            : 1.39
% 7.40/2.62  Inferencing          : 0.46
% 7.40/2.62  Reduction            : 0.56
% 7.40/2.62  Demodulation         : 0.42
% 7.40/2.62  BG Simplification    : 0.05
% 7.40/2.62  Subsumption          : 0.24
% 7.40/2.62  Abstraction          : 0.06
% 7.40/2.62  MUC search           : 0.00
% 7.40/2.62  Cooper               : 0.00
% 7.40/2.62  Total                : 1.84
% 7.40/2.62  Index Insertion      : 0.00
% 7.40/2.62  Index Deletion       : 0.00
% 7.40/2.62  Index Matching       : 0.00
% 7.40/2.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
