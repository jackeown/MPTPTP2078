%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:38 EST 2020

% Result     : Theorem 36.39s
% Output     : CNFRefutation 36.59s
% Verified   : 
% Statistics : Number of formulae       :  267 (1511 expanded)
%              Number of leaves         :   49 ( 496 expanded)
%              Depth                    :   14
%              Number of atoms          :  453 (4710 expanded)
%              Number of equality atoms :  150 ( 899 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_170,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ~ v1_xboole_0(D)
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,A,D)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,D))) )
           => ( ( r1_tarski(B,A)
                & r1_tarski(k7_relset_1(A,D,E,B),C) )
             => ( v1_funct_1(k2_partfun1(A,D,E,B))
                & v1_funct_2(k2_partfun1(A,D,E,B),B,C)
                & m1_subset_1(k2_partfun1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_149,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_81,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_143,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_135,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_86,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_82,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_162055,plain,(
    ! [A_6018,B_6019,C_6020,D_6021] :
      ( k2_partfun1(A_6018,B_6019,C_6020,D_6021) = k7_relat_1(C_6020,D_6021)
      | ~ m1_subset_1(C_6020,k1_zfmisc_1(k2_zfmisc_1(A_6018,B_6019)))
      | ~ v1_funct_1(C_6020) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_162064,plain,(
    ! [D_6021] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_6021) = k7_relat_1('#skF_5',D_6021)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_82,c_162055])).

tff(c_162073,plain,(
    ! [D_6021] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_6021) = k7_relat_1('#skF_5',D_6021) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_162064])).

tff(c_40,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_201,plain,(
    ! [B_73,A_74] :
      ( v1_relat_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_207,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(resolution,[status(thm)],[c_82,c_201])).

tff(c_211,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_207])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_150917,plain,(
    ! [A_5438,B_5439,C_5440,D_5441] :
      ( k7_relset_1(A_5438,B_5439,C_5440,D_5441) = k9_relat_1(C_5440,D_5441)
      | ~ m1_subset_1(C_5440,k1_zfmisc_1(k2_zfmisc_1(A_5438,B_5439))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_150929,plain,(
    ! [D_5442] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_5442) = k9_relat_1('#skF_5',D_5442) ),
    inference(resolution,[status(thm)],[c_82,c_150917])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_146064,plain,(
    ! [A_5166,B_5167,C_5168,D_5169] :
      ( k2_partfun1(A_5166,B_5167,C_5168,D_5169) = k7_relat_1(C_5168,D_5169)
      | ~ m1_subset_1(C_5168,k1_zfmisc_1(k2_zfmisc_1(A_5166,B_5167)))
      | ~ v1_funct_1(C_5168) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_146075,plain,(
    ! [D_5169] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_5169) = k7_relat_1('#skF_5',D_5169)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_82,c_146064])).

tff(c_146085,plain,(
    ! [D_5169] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_5169) = k7_relat_1('#skF_5',D_5169) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_146075])).

tff(c_92335,plain,(
    ! [A_3435,B_3436,C_3437,D_3438] :
      ( k2_partfun1(A_3435,B_3436,C_3437,D_3438) = k7_relat_1(C_3437,D_3438)
      | ~ m1_subset_1(C_3437,k1_zfmisc_1(k2_zfmisc_1(A_3435,B_3436)))
      | ~ v1_funct_1(C_3437) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_92342,plain,(
    ! [D_3438] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_3438) = k7_relat_1('#skF_5',D_3438)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_82,c_92335])).

tff(c_92348,plain,(
    ! [D_3438] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_3438) = k7_relat_1('#skF_5',D_3438) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_92342])).

tff(c_93322,plain,(
    ! [A_3473,B_3474,C_3475,D_3476] :
      ( m1_subset_1(k2_partfun1(A_3473,B_3474,C_3475,D_3476),k1_zfmisc_1(k2_zfmisc_1(A_3473,B_3474)))
      | ~ m1_subset_1(C_3475,k1_zfmisc_1(k2_zfmisc_1(A_3473,B_3474)))
      | ~ v1_funct_1(C_3475) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_93352,plain,(
    ! [D_3438] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_3438),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92348,c_93322])).

tff(c_93375,plain,(
    ! [D_3477] : m1_subset_1(k7_relat_1('#skF_5',D_3477),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_93352])).

tff(c_28,plain,(
    ! [B_16,A_14] :
      ( v1_relat_1(B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_14))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_93399,plain,(
    ! [D_3477] :
      ( v1_relat_1(k7_relat_1('#skF_5',D_3477))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_93375,c_28])).

tff(c_93417,plain,(
    ! [D_3477] : v1_relat_1(k7_relat_1('#skF_5',D_3477)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_93399])).

tff(c_84,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_85183,plain,(
    ! [A_3062,B_3063,C_3064] :
      ( k1_relset_1(A_3062,B_3063,C_3064) = k1_relat_1(C_3064)
      | ~ m1_subset_1(C_3064,k1_zfmisc_1(k2_zfmisc_1(A_3062,B_3063))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_85198,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_85183])).

tff(c_92637,plain,(
    ! [B_3454,A_3455,C_3456] :
      ( k1_xboole_0 = B_3454
      | k1_relset_1(A_3455,B_3454,C_3456) = A_3455
      | ~ v1_funct_2(C_3456,A_3455,B_3454)
      | ~ m1_subset_1(C_3456,k1_zfmisc_1(k2_zfmisc_1(A_3455,B_3454))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_92650,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_92637])).

tff(c_92659,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_85198,c_92650])).

tff(c_92660,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_92659])).

tff(c_80,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_139,plain,(
    ! [A_67,B_68] :
      ( k2_xboole_0(A_67,B_68) = B_68
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_150,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_80,c_139])).

tff(c_2415,plain,(
    ! [A_247,C_248,B_249] :
      ( r1_tarski(A_247,C_248)
      | ~ r1_tarski(k2_xboole_0(A_247,B_249),C_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2421,plain,(
    ! [C_248] :
      ( r1_tarski('#skF_2',C_248)
      | ~ r1_tarski('#skF_1',C_248) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_2415])).

tff(c_84871,plain,(
    ! [B_3048,A_3049] :
      ( k1_relat_1(k7_relat_1(B_3048,A_3049)) = A_3049
      | ~ r1_tarski(A_3049,k1_relat_1(B_3048))
      | ~ v1_relat_1(B_3048) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_84911,plain,(
    ! [B_3048] :
      ( k1_relat_1(k7_relat_1(B_3048,'#skF_2')) = '#skF_2'
      | ~ v1_relat_1(B_3048)
      | ~ r1_tarski('#skF_1',k1_relat_1(B_3048)) ) ),
    inference(resolution,[status(thm)],[c_2421,c_84871])).

tff(c_92671,plain,
    ( k1_relat_1(k7_relat_1('#skF_5','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_5')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92660,c_84911])).

tff(c_92704,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_211,c_92671])).

tff(c_84082,plain,(
    ! [B_2997,A_2998] :
      ( k2_relat_1(k7_relat_1(B_2997,A_2998)) = k9_relat_1(B_2997,A_2998)
      | ~ v1_relat_1(B_2997) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2478,plain,(
    ! [B_253,A_254] :
      ( v5_relat_1(B_253,A_254)
      | ~ r1_tarski(k2_relat_1(B_253),A_254)
      | ~ v1_relat_1(B_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2488,plain,(
    ! [B_253] :
      ( v5_relat_1(B_253,k2_relat_1(B_253))
      | ~ v1_relat_1(B_253) ) ),
    inference(resolution,[status(thm)],[c_8,c_2478])).

tff(c_138551,plain,(
    ! [B_4875,A_4876] :
      ( v5_relat_1(k7_relat_1(B_4875,A_4876),k9_relat_1(B_4875,A_4876))
      | ~ v1_relat_1(k7_relat_1(B_4875,A_4876))
      | ~ v1_relat_1(B_4875) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84082,c_2488])).

tff(c_92171,plain,(
    ! [A_3428,B_3429,C_3430,D_3431] :
      ( k7_relset_1(A_3428,B_3429,C_3430,D_3431) = k9_relat_1(C_3430,D_3431)
      | ~ m1_subset_1(C_3430,k1_zfmisc_1(k2_zfmisc_1(A_3428,B_3429))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_92182,plain,(
    ! [D_3431] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_3431) = k9_relat_1('#skF_5',D_3431) ),
    inference(resolution,[status(thm)],[c_82,c_92171])).

tff(c_78,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_187,plain,(
    k2_xboole_0(k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_78,c_12])).

tff(c_92189,plain,(
    k2_xboole_0(k9_relat_1('#skF_5','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92182,c_187])).

tff(c_2597,plain,(
    ! [B_264,A_265] :
      ( r1_tarski(k2_relat_1(B_264),A_265)
      | ~ v5_relat_1(B_264,A_265)
      | ~ v1_relat_1(B_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_85442,plain,(
    ! [B_3083,A_3084] :
      ( k2_xboole_0(k2_relat_1(B_3083),A_3084) = A_3084
      | ~ v5_relat_1(B_3083,A_3084)
      | ~ v1_relat_1(B_3083) ) ),
    inference(resolution,[status(thm)],[c_2597,c_12])).

tff(c_2431,plain,(
    ! [A_250,B_251] : r1_tarski(A_250,k2_xboole_0(A_250,B_251)) ),
    inference(resolution,[status(thm)],[c_8,c_2415])).

tff(c_10,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2453,plain,(
    ! [A_3,B_4,B_251] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_251)) ),
    inference(resolution,[status(thm)],[c_2431,c_10])).

tff(c_110349,plain,(
    ! [B_4146,A_4147,B_4148] :
      ( r1_tarski(k2_relat_1(B_4146),k2_xboole_0(A_4147,B_4148))
      | ~ v5_relat_1(B_4146,A_4147)
      | ~ v1_relat_1(B_4146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85442,c_2453])).

tff(c_110390,plain,(
    ! [B_4146] :
      ( r1_tarski(k2_relat_1(B_4146),'#skF_3')
      | ~ v5_relat_1(B_4146,k9_relat_1('#skF_5','#skF_2'))
      | ~ v1_relat_1(B_4146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92189,c_110349])).

tff(c_138566,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_138551,c_110390])).

tff(c_138697,plain,(
    r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_93417,c_138566])).

tff(c_92436,plain,(
    ! [C_3442,A_3443,B_3444] :
      ( m1_subset_1(C_3442,k1_zfmisc_1(k2_zfmisc_1(A_3443,B_3444)))
      | ~ r1_tarski(k2_relat_1(C_3442),B_3444)
      | ~ r1_tarski(k1_relat_1(C_3442),A_3443)
      | ~ v1_relat_1(C_3442) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_92477,plain,(
    ! [C_3442,A_3443,B_3444] :
      ( r1_tarski(C_3442,k2_zfmisc_1(A_3443,B_3444))
      | ~ r1_tarski(k2_relat_1(C_3442),B_3444)
      | ~ r1_tarski(k1_relat_1(C_3442),A_3443)
      | ~ v1_relat_1(C_3442) ) ),
    inference(resolution,[status(thm)],[c_92436,c_24])).

tff(c_138796,plain,(
    ! [A_3443] :
      ( r1_tarski(k7_relat_1('#skF_5','#skF_2'),k2_zfmisc_1(A_3443,'#skF_3'))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),A_3443)
      | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_138697,c_92477])).

tff(c_141155,plain,(
    ! [A_4906] :
      ( r1_tarski(k7_relat_1('#skF_5','#skF_2'),k2_zfmisc_1(A_4906,'#skF_3'))
      | ~ r1_tarski('#skF_2',A_4906) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93417,c_92704,c_138796])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2395,plain,(
    ! [A_243,B_244,C_245,D_246] :
      ( v1_funct_1(k2_partfun1(A_243,B_244,C_245,D_246))
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244)))
      | ~ v1_funct_1(C_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2402,plain,(
    ! [D_246] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_246))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_82,c_2395])).

tff(c_2408,plain,(
    ! [D_246] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_246)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2402])).

tff(c_76,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_267,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_2411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2408,c_267])).

tff(c_2412,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_84226,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2412])).

tff(c_84610,plain,(
    ~ r1_tarski(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_84226])).

tff(c_92350,plain,(
    ~ r1_tarski(k7_relat_1('#skF_5','#skF_2'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92348,c_84610])).

tff(c_141181,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_141155,c_92350])).

tff(c_141220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_141181])).

tff(c_141221,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_92659])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_141262,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141221,c_2])).

tff(c_141265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_141262])).

tff(c_141267,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2412])).

tff(c_146093,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146085,c_141267])).

tff(c_52,plain,(
    ! [A_34,B_35,C_36] :
      ( k1_relset_1(A_34,B_35,C_36) = k1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_146200,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = k1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_146093,c_52])).

tff(c_141266,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_2412])).

tff(c_146094,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146085,c_141266])).

tff(c_64,plain,(
    ! [B_45,C_46,A_44] :
      ( k1_xboole_0 = B_45
      | v1_funct_2(C_46,A_44,B_45)
      | k1_relset_1(A_44,B_45,C_46) != A_44
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_146168,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_146093,c_64])).

tff(c_146192,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_146094,c_146168])).

tff(c_146274,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_146192])).

tff(c_146275,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146200,c_146274])).

tff(c_142595,plain,(
    ! [A_4983,B_4984,C_4985] :
      ( k1_relset_1(A_4983,B_4984,C_4985) = k1_relat_1(C_4985)
      | ~ m1_subset_1(C_4985,k1_zfmisc_1(k2_zfmisc_1(A_4983,B_4984))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_142614,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_142595])).

tff(c_146314,plain,(
    ! [B_5177,A_5178,C_5179] :
      ( k1_xboole_0 = B_5177
      | k1_relset_1(A_5178,B_5177,C_5179) = A_5178
      | ~ v1_funct_2(C_5179,A_5178,B_5177)
      | ~ m1_subset_1(C_5179,k1_zfmisc_1(k2_zfmisc_1(A_5178,B_5177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_146330,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_146314])).

tff(c_146342,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_142614,c_146330])).

tff(c_146343,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_146342])).

tff(c_141980,plain,(
    ! [B_4954,A_4955] :
      ( k1_relat_1(k7_relat_1(B_4954,A_4955)) = A_4955
      | ~ r1_tarski(A_4955,k1_relat_1(B_4954))
      | ~ v1_relat_1(B_4954) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_142020,plain,(
    ! [B_4954] :
      ( k1_relat_1(k7_relat_1(B_4954,'#skF_2')) = '#skF_2'
      | ~ v1_relat_1(B_4954)
      | ~ r1_tarski('#skF_1',k1_relat_1(B_4954)) ) ),
    inference(resolution,[status(thm)],[c_2421,c_141980])).

tff(c_146354,plain,
    ( k1_relat_1(k7_relat_1('#skF_5','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_5')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_146343,c_142020])).

tff(c_146387,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_211,c_146354])).

tff(c_146389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146275,c_146387])).

tff(c_146390,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_146342])).

tff(c_146432,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146390,c_2])).

tff(c_146435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_146432])).

tff(c_146436,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_146192])).

tff(c_141784,plain,(
    ! [C_4948] :
      ( r1_tarski(k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2'),C_4948)
      | ~ r1_tarski('#skF_3',C_4948) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_10])).

tff(c_16,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_141822,plain,
    ( k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2') = k1_xboole_0
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_141784,c_16])).

tff(c_141979,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_141822])).

tff(c_146458,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146436,c_141979])).

tff(c_146485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_146458])).

tff(c_146487,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_141822])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_146495,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_146487,c_4])).

tff(c_146513,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_146495])).

tff(c_146542,plain,(
    ! [A_8] : r1_tarski('#skF_3',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146513,c_14])).

tff(c_248,plain,(
    ! [B_79,A_80] :
      ( B_79 = A_80
      | ~ r1_tarski(B_79,A_80)
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_260,plain,
    ( k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2') = '#skF_3'
    | ~ r1_tarski('#skF_3',k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_248])).

tff(c_84030,plain,(
    ~ r1_tarski('#skF_3',k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_146610,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146542,c_84030])).

tff(c_146611,plain,(
    k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_150935,plain,(
    k9_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_150929,c_146611])).

tff(c_42,plain,(
    ! [B_26,A_25] :
      ( k2_relat_1(k7_relat_1(B_26,A_25)) = k9_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_151147,plain,(
    ! [A_5455,B_5456,C_5457,D_5458] :
      ( k2_partfun1(A_5455,B_5456,C_5457,D_5458) = k7_relat_1(C_5457,D_5458)
      | ~ m1_subset_1(C_5457,k1_zfmisc_1(k2_zfmisc_1(A_5455,B_5456)))
      | ~ v1_funct_1(C_5457) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_151154,plain,(
    ! [D_5458] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_5458) = k7_relat_1('#skF_5',D_5458)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_82,c_151147])).

tff(c_151160,plain,(
    ! [D_5458] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_5458) = k7_relat_1('#skF_5',D_5458) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_151154])).

tff(c_151996,plain,(
    ! [A_5506,B_5507,C_5508,D_5509] :
      ( m1_subset_1(k2_partfun1(A_5506,B_5507,C_5508,D_5509),k1_zfmisc_1(k2_zfmisc_1(A_5506,B_5507)))
      | ~ m1_subset_1(C_5508,k1_zfmisc_1(k2_zfmisc_1(A_5506,B_5507)))
      | ~ v1_funct_1(C_5508) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_152026,plain,(
    ! [D_5458] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_5458),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151160,c_151996])).

tff(c_152127,plain,(
    ! [D_5513] : m1_subset_1(k7_relat_1('#skF_5',D_5513),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_152026])).

tff(c_152151,plain,(
    ! [D_5513] :
      ( v1_relat_1(k7_relat_1('#skF_5',D_5513))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_152127,c_28])).

tff(c_152169,plain,(
    ! [D_5513] : v1_relat_1(k7_relat_1('#skF_5',D_5513)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_152151])).

tff(c_147734,plain,(
    ! [A_5258,B_5259,C_5260] :
      ( k1_relset_1(A_5258,B_5259,C_5260) = k1_relat_1(C_5260)
      | ~ m1_subset_1(C_5260,k1_zfmisc_1(k2_zfmisc_1(A_5258,B_5259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_147749,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_147734])).

tff(c_151525,plain,(
    ! [B_5495,A_5496,C_5497] :
      ( k1_xboole_0 = B_5495
      | k1_relset_1(A_5496,B_5495,C_5497) = A_5496
      | ~ v1_funct_2(C_5497,A_5496,B_5495)
      | ~ m1_subset_1(C_5497,k1_zfmisc_1(k2_zfmisc_1(A_5496,B_5495))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_151538,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_151525])).

tff(c_151547,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_147749,c_151538])).

tff(c_151548,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_151547])).

tff(c_147294,plain,(
    ! [B_5231,A_5232] :
      ( k1_relat_1(k7_relat_1(B_5231,A_5232)) = A_5232
      | ~ r1_tarski(A_5232,k1_relat_1(B_5231))
      | ~ v1_relat_1(B_5231) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_147329,plain,(
    ! [B_5231] :
      ( k1_relat_1(k7_relat_1(B_5231,'#skF_2')) = '#skF_2'
      | ~ v1_relat_1(B_5231)
      | ~ r1_tarski('#skF_1',k1_relat_1(B_5231)) ) ),
    inference(resolution,[status(thm)],[c_2421,c_147294])).

tff(c_151574,plain,
    ( k1_relat_1(k7_relat_1('#skF_5','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_5')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_151548,c_147329])).

tff(c_151614,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_211,c_151574])).

tff(c_151278,plain,(
    ! [C_5472,A_5473,B_5474] :
      ( m1_subset_1(C_5472,k1_zfmisc_1(k2_zfmisc_1(A_5473,B_5474)))
      | ~ r1_tarski(k2_relat_1(C_5472),B_5474)
      | ~ r1_tarski(k1_relat_1(C_5472),A_5473)
      | ~ v1_relat_1(C_5472) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_146623,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2412])).

tff(c_151163,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151160,c_146623])).

tff(c_151309,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_151278,c_151163])).

tff(c_153367,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152169,c_8,c_151614,c_151309])).

tff(c_153370,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_153367])).

tff(c_153376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_8,c_150935,c_153370])).

tff(c_153377,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_151547])).

tff(c_153421,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153377,c_2])).

tff(c_153424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_153421])).

tff(c_153425,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_2412])).

tff(c_162085,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162073,c_153425])).

tff(c_153426,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2412])).

tff(c_154636,plain,(
    ! [A_5631,B_5632,C_5633] :
      ( k1_relset_1(A_5631,B_5632,C_5633) = k1_relat_1(C_5633)
      | ~ m1_subset_1(C_5633,k1_zfmisc_1(k2_zfmisc_1(A_5631,B_5632))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_154653,plain,(
    k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) = k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_153426,c_154636])).

tff(c_162079,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = k1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162073,c_162073,c_154653])).

tff(c_162084,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162073,c_153426])).

tff(c_162317,plain,(
    ! [B_6032,C_6033,A_6034] :
      ( k1_xboole_0 = B_6032
      | v1_funct_2(C_6033,A_6034,B_6032)
      | k1_relset_1(A_6034,B_6032,C_6033) != A_6034
      | ~ m1_subset_1(C_6033,k1_zfmisc_1(k2_zfmisc_1(A_6034,B_6032))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_162320,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_162084,c_162317])).

tff(c_162338,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162079,c_162320])).

tff(c_162339,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_162085,c_162338])).

tff(c_162345,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_162339])).

tff(c_154655,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_154636])).

tff(c_162424,plain,(
    ! [B_6037,A_6038,C_6039] :
      ( k1_xboole_0 = B_6037
      | k1_relset_1(A_6038,B_6037,C_6039) = A_6038
      | ~ v1_funct_2(C_6039,A_6038,B_6037)
      | ~ m1_subset_1(C_6039,k1_zfmisc_1(k2_zfmisc_1(A_6038,B_6037))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_162440,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_162424])).

tff(c_162452,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_154655,c_162440])).

tff(c_162453,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_162452])).

tff(c_154417,plain,(
    ! [B_5620,A_5621] :
      ( k1_relat_1(k7_relat_1(B_5620,A_5621)) = A_5621
      | ~ r1_tarski(A_5621,k1_relat_1(B_5620))
      | ~ v1_relat_1(B_5620) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_154452,plain,(
    ! [B_5620] :
      ( k1_relat_1(k7_relat_1(B_5620,'#skF_2')) = '#skF_2'
      | ~ v1_relat_1(B_5620)
      | ~ r1_tarski('#skF_1',k1_relat_1(B_5620)) ) ),
    inference(resolution,[status(thm)],[c_2421,c_154417])).

tff(c_162470,plain,
    ( k1_relat_1(k7_relat_1('#skF_5','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_5')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_162453,c_154452])).

tff(c_162504,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_211,c_162470])).

tff(c_162506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162345,c_162504])).

tff(c_162507,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_162452])).

tff(c_162550,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162507,c_2])).

tff(c_162553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_162550])).

tff(c_162554,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_162339])).

tff(c_97,plain,(
    ! [B_60] : k2_zfmisc_1(k1_xboole_0,B_60) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_101,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_40])).

tff(c_22,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_153787,plain,(
    ! [C_5579,A_5580,B_5581] :
      ( v4_relat_1(C_5579,A_5580)
      | ~ m1_subset_1(C_5579,k1_zfmisc_1(k2_zfmisc_1(A_5580,B_5581))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_153810,plain,(
    ! [A_5586,A_5587,B_5588] :
      ( v4_relat_1(A_5586,A_5587)
      | ~ r1_tarski(A_5586,k2_zfmisc_1(A_5587,B_5588)) ) ),
    inference(resolution,[status(thm)],[c_26,c_153787])).

tff(c_153840,plain,(
    ! [A_5587,B_5588] : v4_relat_1(k2_zfmisc_1(A_5587,B_5588),A_5587) ),
    inference(resolution,[status(thm)],[c_8,c_153810])).

tff(c_153859,plain,(
    ! [B_5594,A_5595] :
      ( r1_tarski(k1_relat_1(B_5594),A_5595)
      | ~ v4_relat_1(B_5594,A_5595)
      | ~ v1_relat_1(B_5594) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_153899,plain,(
    ! [B_5596] :
      ( k1_relat_1(B_5596) = k1_xboole_0
      | ~ v4_relat_1(B_5596,k1_xboole_0)
      | ~ v1_relat_1(B_5596) ) ),
    inference(resolution,[status(thm)],[c_153859,c_16])).

tff(c_153903,plain,(
    ! [B_5588] :
      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_5588)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,B_5588)) ) ),
    inference(resolution,[status(thm)],[c_153840,c_153899])).

tff(c_153914,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_22,c_22,c_153903])).

tff(c_20,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_58,plain,(
    ! [A_44] :
      ( v1_funct_2(k1_xboole_0,A_44,k1_xboole_0)
      | k1_xboole_0 = A_44
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_44,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_92,plain,(
    ! [A_44] :
      ( v1_funct_2(k1_xboole_0,A_44,k1_xboole_0)
      | k1_xboole_0 = A_44
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_58])).

tff(c_154180,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_154183,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_154180])).

tff(c_154187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_154183])).

tff(c_154189,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_154665,plain,(
    ! [B_5634,C_5635] :
      ( k1_relset_1(k1_xboole_0,B_5634,C_5635) = k1_relat_1(C_5635)
      | ~ m1_subset_1(C_5635,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_154636])).

tff(c_154667,plain,(
    ! [B_5634] : k1_relset_1(k1_xboole_0,B_5634,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_154189,c_154665])).

tff(c_154672,plain,(
    ! [B_5634] : k1_relset_1(k1_xboole_0,B_5634,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153914,c_154667])).

tff(c_62,plain,(
    ! [C_46,B_45] :
      ( v1_funct_2(C_46,k1_xboole_0,B_45)
      | k1_relset_1(k1_xboole_0,B_45,C_46) != k1_xboole_0
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_161494,plain,(
    ! [C_5973,B_5974] :
      ( v1_funct_2(C_5973,k1_xboole_0,B_5974)
      | k1_relset_1(k1_xboole_0,B_5974,C_5973) != k1_xboole_0
      | ~ m1_subset_1(C_5973,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_62])).

tff(c_161496,plain,(
    ! [B_5974] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_5974)
      | k1_relset_1(k1_xboole_0,B_5974,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_154189,c_161494])).

tff(c_161502,plain,(
    ! [B_5974] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_5974) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154672,c_161496])).

tff(c_162572,plain,(
    ! [B_5974] : v1_funct_2('#skF_3','#skF_3',B_5974) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162554,c_162554,c_161502])).

tff(c_162586,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162554,c_162554,c_153914])).

tff(c_162601,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162554,c_162554,c_20])).

tff(c_153961,plain,(
    r1_tarski(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_153426,c_24])).

tff(c_162080,plain,(
    r1_tarski(k7_relat_1('#skF_5','#skF_2'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162073,c_153961])).

tff(c_162928,plain,(
    r1_tarski(k7_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162601,c_162080])).

tff(c_162600,plain,(
    ! [A_9] :
      ( A_9 = '#skF_3'
      | ~ r1_tarski(A_9,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162554,c_162554,c_16])).

tff(c_163265,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_162928,c_162600])).

tff(c_162555,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_162339])).

tff(c_163296,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163265,c_162555])).

tff(c_163305,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162586,c_163296])).

tff(c_163302,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163265,c_162085])).

tff(c_163388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162572,c_163305,c_163302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:46:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.39/25.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.39/25.75  
% 36.39/25.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.39/25.75  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 36.39/25.75  
% 36.39/25.75  %Foreground sorts:
% 36.39/25.75  
% 36.39/25.75  
% 36.39/25.75  %Background operators:
% 36.39/25.75  
% 36.39/25.75  
% 36.39/25.75  %Foreground operators:
% 36.39/25.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 36.39/25.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.39/25.75  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 36.39/25.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 36.39/25.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 36.39/25.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 36.39/25.75  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 36.39/25.75  tff('#skF_5', type, '#skF_5': $i).
% 36.39/25.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 36.39/25.75  tff('#skF_2', type, '#skF_2': $i).
% 36.39/25.75  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 36.39/25.75  tff('#skF_3', type, '#skF_3': $i).
% 36.39/25.75  tff('#skF_1', type, '#skF_1': $i).
% 36.39/25.75  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 36.39/25.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 36.39/25.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 36.39/25.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.39/25.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 36.39/25.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 36.39/25.75  tff('#skF_4', type, '#skF_4': $i).
% 36.39/25.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.39/25.75  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 36.39/25.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 36.39/25.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 36.39/25.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 36.39/25.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 36.39/25.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 36.39/25.75  
% 36.59/25.78  tff(f_170, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_funct_2)).
% 36.59/25.78  tff(f_149, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 36.59/25.78  tff(f_81, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 36.59/25.78  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 36.59/25.78  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 36.59/25.78  tff(f_109, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 36.59/25.78  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 36.59/25.78  tff(f_143, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 36.59/25.78  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 36.59/25.78  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 36.59/25.78  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 36.59/25.78  tff(f_36, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 36.59/25.78  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 36.59/25.78  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 36.59/25.78  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 36.59/25.78  tff(f_117, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 36.59/25.78  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 36.59/25.78  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 36.59/25.78  tff(f_46, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 36.59/25.78  tff(f_52, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 36.59/25.78  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 36.59/25.78  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 36.59/25.78  tff(c_88, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 36.59/25.78  tff(c_86, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 36.59/25.78  tff(c_82, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 36.59/25.78  tff(c_162055, plain, (![A_6018, B_6019, C_6020, D_6021]: (k2_partfun1(A_6018, B_6019, C_6020, D_6021)=k7_relat_1(C_6020, D_6021) | ~m1_subset_1(C_6020, k1_zfmisc_1(k2_zfmisc_1(A_6018, B_6019))) | ~v1_funct_1(C_6020))), inference(cnfTransformation, [status(thm)], [f_149])).
% 36.59/25.78  tff(c_162064, plain, (![D_6021]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_6021)=k7_relat_1('#skF_5', D_6021) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_82, c_162055])).
% 36.59/25.78  tff(c_162073, plain, (![D_6021]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_6021)=k7_relat_1('#skF_5', D_6021))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_162064])).
% 36.59/25.78  tff(c_40, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 36.59/25.78  tff(c_201, plain, (![B_73, A_74]: (v1_relat_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_63])).
% 36.59/25.78  tff(c_207, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_201])).
% 36.59/25.78  tff(c_211, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_207])).
% 36.59/25.78  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 36.59/25.78  tff(c_150917, plain, (![A_5438, B_5439, C_5440, D_5441]: (k7_relset_1(A_5438, B_5439, C_5440, D_5441)=k9_relat_1(C_5440, D_5441) | ~m1_subset_1(C_5440, k1_zfmisc_1(k2_zfmisc_1(A_5438, B_5439))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 36.59/25.78  tff(c_150929, plain, (![D_5442]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_5442)=k9_relat_1('#skF_5', D_5442))), inference(resolution, [status(thm)], [c_82, c_150917])).
% 36.59/25.78  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 36.59/25.78  tff(c_146064, plain, (![A_5166, B_5167, C_5168, D_5169]: (k2_partfun1(A_5166, B_5167, C_5168, D_5169)=k7_relat_1(C_5168, D_5169) | ~m1_subset_1(C_5168, k1_zfmisc_1(k2_zfmisc_1(A_5166, B_5167))) | ~v1_funct_1(C_5168))), inference(cnfTransformation, [status(thm)], [f_149])).
% 36.59/25.78  tff(c_146075, plain, (![D_5169]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_5169)=k7_relat_1('#skF_5', D_5169) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_82, c_146064])).
% 36.59/25.78  tff(c_146085, plain, (![D_5169]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_5169)=k7_relat_1('#skF_5', D_5169))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_146075])).
% 36.59/25.78  tff(c_92335, plain, (![A_3435, B_3436, C_3437, D_3438]: (k2_partfun1(A_3435, B_3436, C_3437, D_3438)=k7_relat_1(C_3437, D_3438) | ~m1_subset_1(C_3437, k1_zfmisc_1(k2_zfmisc_1(A_3435, B_3436))) | ~v1_funct_1(C_3437))), inference(cnfTransformation, [status(thm)], [f_149])).
% 36.59/25.78  tff(c_92342, plain, (![D_3438]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_3438)=k7_relat_1('#skF_5', D_3438) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_82, c_92335])).
% 36.59/25.78  tff(c_92348, plain, (![D_3438]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_3438)=k7_relat_1('#skF_5', D_3438))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_92342])).
% 36.59/25.78  tff(c_93322, plain, (![A_3473, B_3474, C_3475, D_3476]: (m1_subset_1(k2_partfun1(A_3473, B_3474, C_3475, D_3476), k1_zfmisc_1(k2_zfmisc_1(A_3473, B_3474))) | ~m1_subset_1(C_3475, k1_zfmisc_1(k2_zfmisc_1(A_3473, B_3474))) | ~v1_funct_1(C_3475))), inference(cnfTransformation, [status(thm)], [f_143])).
% 36.59/25.78  tff(c_93352, plain, (![D_3438]: (m1_subset_1(k7_relat_1('#skF_5', D_3438), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_92348, c_93322])).
% 36.59/25.78  tff(c_93375, plain, (![D_3477]: (m1_subset_1(k7_relat_1('#skF_5', D_3477), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_93352])).
% 36.59/25.78  tff(c_28, plain, (![B_16, A_14]: (v1_relat_1(B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_14)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 36.59/25.78  tff(c_93399, plain, (![D_3477]: (v1_relat_1(k7_relat_1('#skF_5', D_3477)) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(resolution, [status(thm)], [c_93375, c_28])).
% 36.59/25.78  tff(c_93417, plain, (![D_3477]: (v1_relat_1(k7_relat_1('#skF_5', D_3477)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_93399])).
% 36.59/25.78  tff(c_84, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 36.59/25.78  tff(c_85183, plain, (![A_3062, B_3063, C_3064]: (k1_relset_1(A_3062, B_3063, C_3064)=k1_relat_1(C_3064) | ~m1_subset_1(C_3064, k1_zfmisc_1(k2_zfmisc_1(A_3062, B_3063))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 36.59/25.78  tff(c_85198, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_85183])).
% 36.59/25.78  tff(c_92637, plain, (![B_3454, A_3455, C_3456]: (k1_xboole_0=B_3454 | k1_relset_1(A_3455, B_3454, C_3456)=A_3455 | ~v1_funct_2(C_3456, A_3455, B_3454) | ~m1_subset_1(C_3456, k1_zfmisc_1(k2_zfmisc_1(A_3455, B_3454))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 36.59/25.78  tff(c_92650, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_82, c_92637])).
% 36.59/25.78  tff(c_92659, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_85198, c_92650])).
% 36.59/25.78  tff(c_92660, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_92659])).
% 36.59/25.78  tff(c_80, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 36.59/25.78  tff(c_139, plain, (![A_67, B_68]: (k2_xboole_0(A_67, B_68)=B_68 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_40])).
% 36.59/25.78  tff(c_150, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_80, c_139])).
% 36.59/25.78  tff(c_2415, plain, (![A_247, C_248, B_249]: (r1_tarski(A_247, C_248) | ~r1_tarski(k2_xboole_0(A_247, B_249), C_248))), inference(cnfTransformation, [status(thm)], [f_36])).
% 36.59/25.78  tff(c_2421, plain, (![C_248]: (r1_tarski('#skF_2', C_248) | ~r1_tarski('#skF_1', C_248))), inference(superposition, [status(thm), theory('equality')], [c_150, c_2415])).
% 36.59/25.78  tff(c_84871, plain, (![B_3048, A_3049]: (k1_relat_1(k7_relat_1(B_3048, A_3049))=A_3049 | ~r1_tarski(A_3049, k1_relat_1(B_3048)) | ~v1_relat_1(B_3048))), inference(cnfTransformation, [status(thm)], [f_95])).
% 36.59/25.78  tff(c_84911, plain, (![B_3048]: (k1_relat_1(k7_relat_1(B_3048, '#skF_2'))='#skF_2' | ~v1_relat_1(B_3048) | ~r1_tarski('#skF_1', k1_relat_1(B_3048)))), inference(resolution, [status(thm)], [c_2421, c_84871])).
% 36.59/25.78  tff(c_92671, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_5') | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92660, c_84911])).
% 36.59/25.78  tff(c_92704, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_211, c_92671])).
% 36.59/25.78  tff(c_84082, plain, (![B_2997, A_2998]: (k2_relat_1(k7_relat_1(B_2997, A_2998))=k9_relat_1(B_2997, A_2998) | ~v1_relat_1(B_2997))), inference(cnfTransformation, [status(thm)], [f_85])).
% 36.59/25.78  tff(c_2478, plain, (![B_253, A_254]: (v5_relat_1(B_253, A_254) | ~r1_tarski(k2_relat_1(B_253), A_254) | ~v1_relat_1(B_253))), inference(cnfTransformation, [status(thm)], [f_75])).
% 36.59/25.78  tff(c_2488, plain, (![B_253]: (v5_relat_1(B_253, k2_relat_1(B_253)) | ~v1_relat_1(B_253))), inference(resolution, [status(thm)], [c_8, c_2478])).
% 36.59/25.78  tff(c_138551, plain, (![B_4875, A_4876]: (v5_relat_1(k7_relat_1(B_4875, A_4876), k9_relat_1(B_4875, A_4876)) | ~v1_relat_1(k7_relat_1(B_4875, A_4876)) | ~v1_relat_1(B_4875))), inference(superposition, [status(thm), theory('equality')], [c_84082, c_2488])).
% 36.59/25.78  tff(c_92171, plain, (![A_3428, B_3429, C_3430, D_3431]: (k7_relset_1(A_3428, B_3429, C_3430, D_3431)=k9_relat_1(C_3430, D_3431) | ~m1_subset_1(C_3430, k1_zfmisc_1(k2_zfmisc_1(A_3428, B_3429))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 36.59/25.78  tff(c_92182, plain, (![D_3431]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_3431)=k9_relat_1('#skF_5', D_3431))), inference(resolution, [status(thm)], [c_82, c_92171])).
% 36.59/25.78  tff(c_78, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 36.59/25.78  tff(c_12, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 36.59/25.78  tff(c_187, plain, (k2_xboole_0(k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_78, c_12])).
% 36.59/25.78  tff(c_92189, plain, (k2_xboole_0(k9_relat_1('#skF_5', '#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_92182, c_187])).
% 36.59/25.78  tff(c_2597, plain, (![B_264, A_265]: (r1_tarski(k2_relat_1(B_264), A_265) | ~v5_relat_1(B_264, A_265) | ~v1_relat_1(B_264))), inference(cnfTransformation, [status(thm)], [f_75])).
% 36.59/25.78  tff(c_85442, plain, (![B_3083, A_3084]: (k2_xboole_0(k2_relat_1(B_3083), A_3084)=A_3084 | ~v5_relat_1(B_3083, A_3084) | ~v1_relat_1(B_3083))), inference(resolution, [status(thm)], [c_2597, c_12])).
% 36.59/25.78  tff(c_2431, plain, (![A_250, B_251]: (r1_tarski(A_250, k2_xboole_0(A_250, B_251)))), inference(resolution, [status(thm)], [c_8, c_2415])).
% 36.59/25.78  tff(c_10, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 36.59/25.78  tff(c_2453, plain, (![A_3, B_4, B_251]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_251)))), inference(resolution, [status(thm)], [c_2431, c_10])).
% 36.59/25.78  tff(c_110349, plain, (![B_4146, A_4147, B_4148]: (r1_tarski(k2_relat_1(B_4146), k2_xboole_0(A_4147, B_4148)) | ~v5_relat_1(B_4146, A_4147) | ~v1_relat_1(B_4146))), inference(superposition, [status(thm), theory('equality')], [c_85442, c_2453])).
% 36.59/25.78  tff(c_110390, plain, (![B_4146]: (r1_tarski(k2_relat_1(B_4146), '#skF_3') | ~v5_relat_1(B_4146, k9_relat_1('#skF_5', '#skF_2')) | ~v1_relat_1(B_4146))), inference(superposition, [status(thm), theory('equality')], [c_92189, c_110349])).
% 36.59/25.78  tff(c_138566, plain, (r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_138551, c_110390])).
% 36.59/25.78  tff(c_138697, plain, (r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_93417, c_138566])).
% 36.59/25.78  tff(c_92436, plain, (![C_3442, A_3443, B_3444]: (m1_subset_1(C_3442, k1_zfmisc_1(k2_zfmisc_1(A_3443, B_3444))) | ~r1_tarski(k2_relat_1(C_3442), B_3444) | ~r1_tarski(k1_relat_1(C_3442), A_3443) | ~v1_relat_1(C_3442))), inference(cnfTransformation, [status(thm)], [f_117])).
% 36.59/25.78  tff(c_24, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 36.59/25.78  tff(c_92477, plain, (![C_3442, A_3443, B_3444]: (r1_tarski(C_3442, k2_zfmisc_1(A_3443, B_3444)) | ~r1_tarski(k2_relat_1(C_3442), B_3444) | ~r1_tarski(k1_relat_1(C_3442), A_3443) | ~v1_relat_1(C_3442))), inference(resolution, [status(thm)], [c_92436, c_24])).
% 36.59/25.78  tff(c_138796, plain, (![A_3443]: (r1_tarski(k7_relat_1('#skF_5', '#skF_2'), k2_zfmisc_1(A_3443, '#skF_3')) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), A_3443) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2')))), inference(resolution, [status(thm)], [c_138697, c_92477])).
% 36.59/25.78  tff(c_141155, plain, (![A_4906]: (r1_tarski(k7_relat_1('#skF_5', '#skF_2'), k2_zfmisc_1(A_4906, '#skF_3')) | ~r1_tarski('#skF_2', A_4906))), inference(demodulation, [status(thm), theory('equality')], [c_93417, c_92704, c_138796])).
% 36.59/25.78  tff(c_26, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 36.59/25.78  tff(c_2395, plain, (![A_243, B_244, C_245, D_246]: (v1_funct_1(k2_partfun1(A_243, B_244, C_245, D_246)) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))) | ~v1_funct_1(C_245))), inference(cnfTransformation, [status(thm)], [f_143])).
% 36.59/25.78  tff(c_2402, plain, (![D_246]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_246)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_82, c_2395])).
% 36.59/25.78  tff(c_2408, plain, (![D_246]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_246)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2402])).
% 36.59/25.78  tff(c_76, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 36.59/25.78  tff(c_267, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_76])).
% 36.59/25.78  tff(c_2411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2408, c_267])).
% 36.59/25.78  tff(c_2412, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_76])).
% 36.59/25.78  tff(c_84226, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_2412])).
% 36.59/25.78  tff(c_84610, plain, (~r1_tarski(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_84226])).
% 36.59/25.78  tff(c_92350, plain, (~r1_tarski(k7_relat_1('#skF_5', '#skF_2'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_92348, c_84610])).
% 36.59/25.78  tff(c_141181, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_141155, c_92350])).
% 36.59/25.78  tff(c_141220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_141181])).
% 36.59/25.78  tff(c_141221, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_92659])).
% 36.59/25.78  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 36.59/25.78  tff(c_141262, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_141221, c_2])).
% 36.59/25.78  tff(c_141265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_141262])).
% 36.59/25.78  tff(c_141267, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_2412])).
% 36.59/25.78  tff(c_146093, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_146085, c_141267])).
% 36.59/25.78  tff(c_52, plain, (![A_34, B_35, C_36]: (k1_relset_1(A_34, B_35, C_36)=k1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 36.59/25.78  tff(c_146200, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_146093, c_52])).
% 36.59/25.78  tff(c_141266, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_2412])).
% 36.59/25.78  tff(c_146094, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_146085, c_141266])).
% 36.59/25.78  tff(c_64, plain, (![B_45, C_46, A_44]: (k1_xboole_0=B_45 | v1_funct_2(C_46, A_44, B_45) | k1_relset_1(A_44, B_45, C_46)!=A_44 | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 36.59/25.78  tff(c_146168, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(resolution, [status(thm)], [c_146093, c_64])).
% 36.59/25.78  tff(c_146192, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_146094, c_146168])).
% 36.59/25.78  tff(c_146274, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_146192])).
% 36.59/25.78  tff(c_146275, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_146200, c_146274])).
% 36.59/25.78  tff(c_142595, plain, (![A_4983, B_4984, C_4985]: (k1_relset_1(A_4983, B_4984, C_4985)=k1_relat_1(C_4985) | ~m1_subset_1(C_4985, k1_zfmisc_1(k2_zfmisc_1(A_4983, B_4984))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 36.59/25.78  tff(c_142614, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_142595])).
% 36.59/25.78  tff(c_146314, plain, (![B_5177, A_5178, C_5179]: (k1_xboole_0=B_5177 | k1_relset_1(A_5178, B_5177, C_5179)=A_5178 | ~v1_funct_2(C_5179, A_5178, B_5177) | ~m1_subset_1(C_5179, k1_zfmisc_1(k2_zfmisc_1(A_5178, B_5177))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 36.59/25.78  tff(c_146330, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_82, c_146314])).
% 36.59/25.78  tff(c_146342, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_142614, c_146330])).
% 36.59/25.78  tff(c_146343, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_146342])).
% 36.59/25.78  tff(c_141980, plain, (![B_4954, A_4955]: (k1_relat_1(k7_relat_1(B_4954, A_4955))=A_4955 | ~r1_tarski(A_4955, k1_relat_1(B_4954)) | ~v1_relat_1(B_4954))), inference(cnfTransformation, [status(thm)], [f_95])).
% 36.59/25.78  tff(c_142020, plain, (![B_4954]: (k1_relat_1(k7_relat_1(B_4954, '#skF_2'))='#skF_2' | ~v1_relat_1(B_4954) | ~r1_tarski('#skF_1', k1_relat_1(B_4954)))), inference(resolution, [status(thm)], [c_2421, c_141980])).
% 36.59/25.78  tff(c_146354, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_5') | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_146343, c_142020])).
% 36.59/25.78  tff(c_146387, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_211, c_146354])).
% 36.59/25.78  tff(c_146389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146275, c_146387])).
% 36.59/25.78  tff(c_146390, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_146342])).
% 36.59/25.78  tff(c_146432, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_146390, c_2])).
% 36.59/25.78  tff(c_146435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_146432])).
% 36.59/25.78  tff(c_146436, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_146192])).
% 36.59/25.78  tff(c_141784, plain, (![C_4948]: (r1_tarski(k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), C_4948) | ~r1_tarski('#skF_3', C_4948))), inference(superposition, [status(thm), theory('equality')], [c_187, c_10])).
% 36.59/25.78  tff(c_16, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_46])).
% 36.59/25.78  tff(c_141822, plain, (k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2')=k1_xboole_0 | ~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_141784, c_16])).
% 36.59/25.78  tff(c_141979, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_141822])).
% 36.59/25.78  tff(c_146458, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_146436, c_141979])).
% 36.59/25.78  tff(c_146485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_146458])).
% 36.59/25.78  tff(c_146487, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_141822])).
% 36.59/25.78  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 36.59/25.78  tff(c_146495, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_146487, c_4])).
% 36.59/25.78  tff(c_146513, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_146495])).
% 36.59/25.78  tff(c_146542, plain, (![A_8]: (r1_tarski('#skF_3', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_146513, c_14])).
% 36.59/25.78  tff(c_248, plain, (![B_79, A_80]: (B_79=A_80 | ~r1_tarski(B_79, A_80) | ~r1_tarski(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_32])).
% 36.59/25.78  tff(c_260, plain, (k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2')='#skF_3' | ~r1_tarski('#skF_3', k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_248])).
% 36.59/25.78  tff(c_84030, plain, (~r1_tarski('#skF_3', k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_260])).
% 36.59/25.78  tff(c_146610, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146542, c_84030])).
% 36.59/25.78  tff(c_146611, plain, (k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_260])).
% 36.59/25.78  tff(c_150935, plain, (k9_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_150929, c_146611])).
% 36.59/25.78  tff(c_42, plain, (![B_26, A_25]: (k2_relat_1(k7_relat_1(B_26, A_25))=k9_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_85])).
% 36.59/25.78  tff(c_151147, plain, (![A_5455, B_5456, C_5457, D_5458]: (k2_partfun1(A_5455, B_5456, C_5457, D_5458)=k7_relat_1(C_5457, D_5458) | ~m1_subset_1(C_5457, k1_zfmisc_1(k2_zfmisc_1(A_5455, B_5456))) | ~v1_funct_1(C_5457))), inference(cnfTransformation, [status(thm)], [f_149])).
% 36.59/25.78  tff(c_151154, plain, (![D_5458]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_5458)=k7_relat_1('#skF_5', D_5458) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_82, c_151147])).
% 36.59/25.78  tff(c_151160, plain, (![D_5458]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_5458)=k7_relat_1('#skF_5', D_5458))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_151154])).
% 36.59/25.78  tff(c_151996, plain, (![A_5506, B_5507, C_5508, D_5509]: (m1_subset_1(k2_partfun1(A_5506, B_5507, C_5508, D_5509), k1_zfmisc_1(k2_zfmisc_1(A_5506, B_5507))) | ~m1_subset_1(C_5508, k1_zfmisc_1(k2_zfmisc_1(A_5506, B_5507))) | ~v1_funct_1(C_5508))), inference(cnfTransformation, [status(thm)], [f_143])).
% 36.59/25.78  tff(c_152026, plain, (![D_5458]: (m1_subset_1(k7_relat_1('#skF_5', D_5458), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_151160, c_151996])).
% 36.59/25.78  tff(c_152127, plain, (![D_5513]: (m1_subset_1(k7_relat_1('#skF_5', D_5513), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_152026])).
% 36.59/25.78  tff(c_152151, plain, (![D_5513]: (v1_relat_1(k7_relat_1('#skF_5', D_5513)) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(resolution, [status(thm)], [c_152127, c_28])).
% 36.59/25.78  tff(c_152169, plain, (![D_5513]: (v1_relat_1(k7_relat_1('#skF_5', D_5513)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_152151])).
% 36.59/25.78  tff(c_147734, plain, (![A_5258, B_5259, C_5260]: (k1_relset_1(A_5258, B_5259, C_5260)=k1_relat_1(C_5260) | ~m1_subset_1(C_5260, k1_zfmisc_1(k2_zfmisc_1(A_5258, B_5259))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 36.59/25.78  tff(c_147749, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_147734])).
% 36.59/25.78  tff(c_151525, plain, (![B_5495, A_5496, C_5497]: (k1_xboole_0=B_5495 | k1_relset_1(A_5496, B_5495, C_5497)=A_5496 | ~v1_funct_2(C_5497, A_5496, B_5495) | ~m1_subset_1(C_5497, k1_zfmisc_1(k2_zfmisc_1(A_5496, B_5495))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 36.59/25.78  tff(c_151538, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_82, c_151525])).
% 36.59/25.78  tff(c_151547, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_147749, c_151538])).
% 36.59/25.78  tff(c_151548, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_151547])).
% 36.59/25.78  tff(c_147294, plain, (![B_5231, A_5232]: (k1_relat_1(k7_relat_1(B_5231, A_5232))=A_5232 | ~r1_tarski(A_5232, k1_relat_1(B_5231)) | ~v1_relat_1(B_5231))), inference(cnfTransformation, [status(thm)], [f_95])).
% 36.59/25.78  tff(c_147329, plain, (![B_5231]: (k1_relat_1(k7_relat_1(B_5231, '#skF_2'))='#skF_2' | ~v1_relat_1(B_5231) | ~r1_tarski('#skF_1', k1_relat_1(B_5231)))), inference(resolution, [status(thm)], [c_2421, c_147294])).
% 36.59/25.78  tff(c_151574, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_5') | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_151548, c_147329])).
% 36.59/25.78  tff(c_151614, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_211, c_151574])).
% 36.59/25.78  tff(c_151278, plain, (![C_5472, A_5473, B_5474]: (m1_subset_1(C_5472, k1_zfmisc_1(k2_zfmisc_1(A_5473, B_5474))) | ~r1_tarski(k2_relat_1(C_5472), B_5474) | ~r1_tarski(k1_relat_1(C_5472), A_5473) | ~v1_relat_1(C_5472))), inference(cnfTransformation, [status(thm)], [f_117])).
% 36.59/25.78  tff(c_146623, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_2412])).
% 36.59/25.78  tff(c_151163, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_151160, c_146623])).
% 36.59/25.78  tff(c_151309, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_151278, c_151163])).
% 36.59/25.78  tff(c_153367, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_152169, c_8, c_151614, c_151309])).
% 36.59/25.78  tff(c_153370, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_42, c_153367])).
% 36.59/25.78  tff(c_153376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_211, c_8, c_150935, c_153370])).
% 36.59/25.78  tff(c_153377, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_151547])).
% 36.59/25.78  tff(c_153421, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_153377, c_2])).
% 36.59/25.78  tff(c_153424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_153421])).
% 36.59/25.78  tff(c_153425, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_2412])).
% 36.59/25.78  tff(c_162085, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_162073, c_153425])).
% 36.59/25.78  tff(c_153426, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_2412])).
% 36.59/25.78  tff(c_154636, plain, (![A_5631, B_5632, C_5633]: (k1_relset_1(A_5631, B_5632, C_5633)=k1_relat_1(C_5633) | ~m1_subset_1(C_5633, k1_zfmisc_1(k2_zfmisc_1(A_5631, B_5632))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 36.59/25.78  tff(c_154653, plain, (k1_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_153426, c_154636])).
% 36.59/25.78  tff(c_162079, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_162073, c_162073, c_154653])).
% 36.59/25.78  tff(c_162084, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_162073, c_153426])).
% 36.59/25.78  tff(c_162317, plain, (![B_6032, C_6033, A_6034]: (k1_xboole_0=B_6032 | v1_funct_2(C_6033, A_6034, B_6032) | k1_relset_1(A_6034, B_6032, C_6033)!=A_6034 | ~m1_subset_1(C_6033, k1_zfmisc_1(k2_zfmisc_1(A_6034, B_6032))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 36.59/25.78  tff(c_162320, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(resolution, [status(thm)], [c_162084, c_162317])).
% 36.59/25.78  tff(c_162338, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_162079, c_162320])).
% 36.59/25.78  tff(c_162339, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_162085, c_162338])).
% 36.59/25.78  tff(c_162345, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_162339])).
% 36.59/25.78  tff(c_154655, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_154636])).
% 36.59/25.78  tff(c_162424, plain, (![B_6037, A_6038, C_6039]: (k1_xboole_0=B_6037 | k1_relset_1(A_6038, B_6037, C_6039)=A_6038 | ~v1_funct_2(C_6039, A_6038, B_6037) | ~m1_subset_1(C_6039, k1_zfmisc_1(k2_zfmisc_1(A_6038, B_6037))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 36.59/25.78  tff(c_162440, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_82, c_162424])).
% 36.59/25.78  tff(c_162452, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_154655, c_162440])).
% 36.59/25.78  tff(c_162453, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_162452])).
% 36.59/25.78  tff(c_154417, plain, (![B_5620, A_5621]: (k1_relat_1(k7_relat_1(B_5620, A_5621))=A_5621 | ~r1_tarski(A_5621, k1_relat_1(B_5620)) | ~v1_relat_1(B_5620))), inference(cnfTransformation, [status(thm)], [f_95])).
% 36.59/25.78  tff(c_154452, plain, (![B_5620]: (k1_relat_1(k7_relat_1(B_5620, '#skF_2'))='#skF_2' | ~v1_relat_1(B_5620) | ~r1_tarski('#skF_1', k1_relat_1(B_5620)))), inference(resolution, [status(thm)], [c_2421, c_154417])).
% 36.59/25.78  tff(c_162470, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_5') | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_162453, c_154452])).
% 36.59/25.78  tff(c_162504, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_211, c_162470])).
% 36.59/25.78  tff(c_162506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162345, c_162504])).
% 36.59/25.78  tff(c_162507, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_162452])).
% 36.59/25.78  tff(c_162550, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_162507, c_2])).
% 36.59/25.78  tff(c_162553, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_162550])).
% 36.59/25.78  tff(c_162554, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_162339])).
% 36.59/25.78  tff(c_97, plain, (![B_60]: (k2_zfmisc_1(k1_xboole_0, B_60)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 36.59/25.78  tff(c_101, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_97, c_40])).
% 36.59/25.78  tff(c_22, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 36.59/25.78  tff(c_153787, plain, (![C_5579, A_5580, B_5581]: (v4_relat_1(C_5579, A_5580) | ~m1_subset_1(C_5579, k1_zfmisc_1(k2_zfmisc_1(A_5580, B_5581))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 36.59/25.78  tff(c_153810, plain, (![A_5586, A_5587, B_5588]: (v4_relat_1(A_5586, A_5587) | ~r1_tarski(A_5586, k2_zfmisc_1(A_5587, B_5588)))), inference(resolution, [status(thm)], [c_26, c_153787])).
% 36.59/25.78  tff(c_153840, plain, (![A_5587, B_5588]: (v4_relat_1(k2_zfmisc_1(A_5587, B_5588), A_5587))), inference(resolution, [status(thm)], [c_8, c_153810])).
% 36.59/25.78  tff(c_153859, plain, (![B_5594, A_5595]: (r1_tarski(k1_relat_1(B_5594), A_5595) | ~v4_relat_1(B_5594, A_5595) | ~v1_relat_1(B_5594))), inference(cnfTransformation, [status(thm)], [f_69])).
% 36.59/25.78  tff(c_153899, plain, (![B_5596]: (k1_relat_1(B_5596)=k1_xboole_0 | ~v4_relat_1(B_5596, k1_xboole_0) | ~v1_relat_1(B_5596))), inference(resolution, [status(thm)], [c_153859, c_16])).
% 36.59/25.78  tff(c_153903, plain, (![B_5588]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_5588))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, B_5588)))), inference(resolution, [status(thm)], [c_153840, c_153899])).
% 36.59/25.78  tff(c_153914, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_101, c_22, c_22, c_153903])).
% 36.59/25.78  tff(c_20, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 36.59/25.78  tff(c_58, plain, (![A_44]: (v1_funct_2(k1_xboole_0, A_44, k1_xboole_0) | k1_xboole_0=A_44 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_44, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 36.59/25.78  tff(c_92, plain, (![A_44]: (v1_funct_2(k1_xboole_0, A_44, k1_xboole_0) | k1_xboole_0=A_44 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_58])).
% 36.59/25.78  tff(c_154180, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_92])).
% 36.59/25.78  tff(c_154183, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_154180])).
% 36.59/25.78  tff(c_154187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_154183])).
% 36.59/25.78  tff(c_154189, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_92])).
% 36.59/25.78  tff(c_154665, plain, (![B_5634, C_5635]: (k1_relset_1(k1_xboole_0, B_5634, C_5635)=k1_relat_1(C_5635) | ~m1_subset_1(C_5635, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_154636])).
% 36.59/25.78  tff(c_154667, plain, (![B_5634]: (k1_relset_1(k1_xboole_0, B_5634, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_154189, c_154665])).
% 36.59/25.78  tff(c_154672, plain, (![B_5634]: (k1_relset_1(k1_xboole_0, B_5634, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_153914, c_154667])).
% 36.59/25.78  tff(c_62, plain, (![C_46, B_45]: (v1_funct_2(C_46, k1_xboole_0, B_45) | k1_relset_1(k1_xboole_0, B_45, C_46)!=k1_xboole_0 | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_45))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 36.59/25.78  tff(c_161494, plain, (![C_5973, B_5974]: (v1_funct_2(C_5973, k1_xboole_0, B_5974) | k1_relset_1(k1_xboole_0, B_5974, C_5973)!=k1_xboole_0 | ~m1_subset_1(C_5973, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_62])).
% 36.59/25.78  tff(c_161496, plain, (![B_5974]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_5974) | k1_relset_1(k1_xboole_0, B_5974, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_154189, c_161494])).
% 36.59/25.78  tff(c_161502, plain, (![B_5974]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_5974))), inference(demodulation, [status(thm), theory('equality')], [c_154672, c_161496])).
% 36.59/25.78  tff(c_162572, plain, (![B_5974]: (v1_funct_2('#skF_3', '#skF_3', B_5974))), inference(demodulation, [status(thm), theory('equality')], [c_162554, c_162554, c_161502])).
% 36.59/25.78  tff(c_162586, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_162554, c_162554, c_153914])).
% 36.59/25.78  tff(c_162601, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_162554, c_162554, c_20])).
% 36.59/25.78  tff(c_153961, plain, (r1_tarski(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_153426, c_24])).
% 36.59/25.78  tff(c_162080, plain, (r1_tarski(k7_relat_1('#skF_5', '#skF_2'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_162073, c_153961])).
% 36.59/25.78  tff(c_162928, plain, (r1_tarski(k7_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_162601, c_162080])).
% 36.59/25.78  tff(c_162600, plain, (![A_9]: (A_9='#skF_3' | ~r1_tarski(A_9, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_162554, c_162554, c_16])).
% 36.59/25.78  tff(c_163265, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_162928, c_162600])).
% 36.59/25.78  tff(c_162555, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))='#skF_2'), inference(splitRight, [status(thm)], [c_162339])).
% 36.59/25.78  tff(c_163296, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_163265, c_162555])).
% 36.59/25.78  tff(c_163305, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_162586, c_163296])).
% 36.59/25.78  tff(c_163302, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_163265, c_162085])).
% 36.59/25.78  tff(c_163388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162572, c_163305, c_163302])).
% 36.59/25.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.59/25.78  
% 36.59/25.78  Inference rules
% 36.59/25.78  ----------------------
% 36.59/25.78  #Ref     : 0
% 36.59/25.78  #Sup     : 37107
% 36.59/25.78  #Fact    : 0
% 36.59/25.78  #Define  : 0
% 36.59/25.78  #Split   : 328
% 36.59/25.79  #Chain   : 0
% 36.59/25.79  #Close   : 0
% 36.59/25.79  
% 36.59/25.79  Ordering : KBO
% 36.59/25.79  
% 36.59/25.79  Simplification rules
% 36.59/25.79  ----------------------
% 36.59/25.79  #Subsume      : 11432
% 36.59/25.79  #Demod        : 31349
% 36.59/25.79  #Tautology    : 11581
% 36.59/25.79  #SimpNegUnit  : 1227
% 36.59/25.79  #BackRed      : 2021
% 36.59/25.79  
% 36.59/25.79  #Partial instantiations: 0
% 36.59/25.79  #Strategies tried      : 1
% 36.59/25.79  
% 36.59/25.79  Timing (in seconds)
% 36.59/25.79  ----------------------
% 36.76/25.79  Preprocessing        : 0.36
% 36.76/25.79  Parsing              : 0.19
% 36.76/25.79  CNF conversion       : 0.02
% 36.76/25.79  Main loop            : 24.61
% 36.76/25.79  Inferencing          : 4.39
% 36.76/25.79  Reduction            : 11.59
% 36.76/25.79  Demodulation         : 9.11
% 36.76/25.79  BG Simplification    : 0.36
% 36.76/25.79  Subsumption          : 6.69
% 36.76/25.79  Abstraction          : 0.53
% 36.76/25.79  MUC search           : 0.00
% 36.76/25.79  Cooper               : 0.00
% 36.76/25.79  Total                : 25.05
% 36.76/25.79  Index Insertion      : 0.00
% 36.76/25.79  Index Deletion       : 0.00
% 36.76/25.79  Index Matching       : 0.00
% 36.76/25.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
