%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:06 EST 2020

% Result     : Theorem 8.26s
% Output     : CNFRefutation 8.35s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 474 expanded)
%              Number of leaves         :   47 ( 181 expanded)
%              Depth                    :   12
%              Number of atoms          :  284 (1503 expanded)
%              Number of equality atoms :   60 ( 150 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_175,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_133,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_65,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_131,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_117,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_121,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_155,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_300,plain,(
    ! [C_97,B_98,A_99] :
      ( v1_xboole_0(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(B_98,A_99)))
      | ~ v1_xboole_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_317,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_300])).

tff(c_321,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_317])).

tff(c_58,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_28,plain,(
    ! [A_13] : v2_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_79,plain,(
    ! [A_13] : v2_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_28])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_846,plain,(
    ! [D_150,B_152,A_148,E_147,F_151,C_149] :
      ( k1_partfun1(A_148,B_152,C_149,D_150,E_147,F_151) = k5_relat_1(E_147,F_151)
      | ~ m1_subset_1(F_151,k1_zfmisc_1(k2_zfmisc_1(C_149,D_150)))
      | ~ v1_funct_1(F_151)
      | ~ m1_subset_1(E_147,k1_zfmisc_1(k2_zfmisc_1(A_148,B_152)))
      | ~ v1_funct_1(E_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_850,plain,(
    ! [A_148,B_152,E_147] :
      ( k1_partfun1(A_148,B_152,'#skF_2','#skF_1',E_147,'#skF_4') = k5_relat_1(E_147,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_147,k1_zfmisc_1(k2_zfmisc_1(A_148,B_152)))
      | ~ v1_funct_1(E_147) ) ),
    inference(resolution,[status(thm)],[c_68,c_846])).

tff(c_1392,plain,(
    ! [A_199,B_200,E_201] :
      ( k1_partfun1(A_199,B_200,'#skF_2','#skF_1',E_201,'#skF_4') = k5_relat_1(E_201,'#skF_4')
      | ~ m1_subset_1(E_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200)))
      | ~ v1_funct_1(E_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_850])).

tff(c_1410,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1392])).

tff(c_1430,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1410])).

tff(c_48,plain,(
    ! [D_37,A_34,F_39,B_35,C_36,E_38] :
      ( m1_subset_1(k1_partfun1(A_34,B_35,C_36,D_37,E_38,F_39),k1_zfmisc_1(k2_zfmisc_1(A_34,D_37)))
      | ~ m1_subset_1(F_39,k1_zfmisc_1(k2_zfmisc_1(C_36,D_37)))
      | ~ v1_funct_1(F_39)
      | ~ m1_subset_1(E_38,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1(E_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1541,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1430,c_48])).

tff(c_1548,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_1541])).

tff(c_54,plain,(
    ! [A_40] : m1_subset_1(k6_partfun1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_66,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_677,plain,(
    ! [D_123,C_124,A_125,B_126] :
      ( D_123 = C_124
      | ~ r2_relset_1(A_125,B_126,C_124,D_123)
      | ~ m1_subset_1(D_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_683,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_677])).

tff(c_694,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_683])).

tff(c_1646,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1548,c_1430,c_1430,c_694])).

tff(c_64,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_109,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_62,plain,(
    ! [B_49,A_48,D_51,C_50,E_53] :
      ( k1_xboole_0 = C_50
      | v2_funct_1(D_51)
      | ~ v2_funct_1(k1_partfun1(A_48,B_49,B_49,C_50,D_51,E_53))
      | ~ m1_subset_1(E_53,k1_zfmisc_1(k2_zfmisc_1(B_49,C_50)))
      | ~ v1_funct_2(E_53,B_49,C_50)
      | ~ v1_funct_1(E_53)
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_2(D_51,A_48,B_49)
      | ~ v1_funct_1(D_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1538,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1430,c_62])).

tff(c_1545,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_70,c_68,c_1538])).

tff(c_1546,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_1545])).

tff(c_1550,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1546])).

tff(c_1652,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1646,c_1550])).

tff(c_1662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_1652])).

tff(c_1663,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1546])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1699,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1663,c_2])).

tff(c_1701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_321,c_1699])).

tff(c_1702,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_1842,plain,(
    ! [A_215] :
      ( v1_xboole_0(k6_partfun1(A_215))
      | ~ v1_xboole_0(A_215) ) ),
    inference(resolution,[status(thm)],[c_54,c_300])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( ~ v1_xboole_0(B_4)
      | B_4 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1710,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_1702,c_10])).

tff(c_1865,plain,(
    ! [A_218] :
      ( k6_partfun1(A_218) = '#skF_4'
      | ~ v1_xboole_0(A_218) ) ),
    inference(resolution,[status(thm)],[c_1842,c_1710])).

tff(c_1873,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1702,c_1865])).

tff(c_1912,plain,(
    v2_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1873,c_79])).

tff(c_138,plain,(
    ! [B_63,A_64] :
      ( ~ v1_xboole_0(B_63)
      | B_63 = A_64
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_141,plain,(
    ! [A_64] :
      ( k1_xboole_0 = A_64
      | ~ v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_2,c_138])).

tff(c_1709,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1702,c_141])).

tff(c_16,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1724,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_4',B_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1709,c_1709,c_16])).

tff(c_1703,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_1716,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1703,c_141])).

tff(c_1732,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1709,c_1716])).

tff(c_1738,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1732,c_74])).

tff(c_1805,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1724,c_1738])).

tff(c_14,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_315,plain,(
    ! [C_97] :
      ( v1_xboole_0(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_300])).

tff(c_320,plain,(
    ! [C_97] :
      ( v1_xboole_0(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_315])).

tff(c_1968,plain,(
    ! [C_223] :
      ( v1_xboole_0(C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1709,c_320])).

tff(c_1977,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1805,c_1968])).

tff(c_1987,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1977,c_1710])).

tff(c_1996,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1987,c_109])).

tff(c_2004,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1912,c_1996])).

tff(c_2005,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2073,plain,(
    ! [C_236,A_237,B_238] :
      ( v1_relat_1(C_236)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2088,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_2073])).

tff(c_2140,plain,(
    ! [C_253,B_254,A_255] :
      ( v5_relat_1(C_253,B_254)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_255,B_254))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2158,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_2140])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2089,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_2073])).

tff(c_26,plain,(
    ! [A_12] : k2_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_80,plain,(
    ! [A_12] : k2_relat_1(k6_partfun1(A_12)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_26])).

tff(c_2737,plain,(
    ! [E_312,B_317,D_315,F_316,C_314,A_313] :
      ( k1_partfun1(A_313,B_317,C_314,D_315,E_312,F_316) = k5_relat_1(E_312,F_316)
      | ~ m1_subset_1(F_316,k1_zfmisc_1(k2_zfmisc_1(C_314,D_315)))
      | ~ v1_funct_1(F_316)
      | ~ m1_subset_1(E_312,k1_zfmisc_1(k2_zfmisc_1(A_313,B_317)))
      | ~ v1_funct_1(E_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2741,plain,(
    ! [A_313,B_317,E_312] :
      ( k1_partfun1(A_313,B_317,'#skF_2','#skF_1',E_312,'#skF_4') = k5_relat_1(E_312,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_312,k1_zfmisc_1(k2_zfmisc_1(A_313,B_317)))
      | ~ v1_funct_1(E_312) ) ),
    inference(resolution,[status(thm)],[c_68,c_2737])).

tff(c_3173,plain,(
    ! [A_356,B_357,E_358] :
      ( k1_partfun1(A_356,B_357,'#skF_2','#skF_1',E_358,'#skF_4') = k5_relat_1(E_358,'#skF_4')
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(A_356,B_357)))
      | ~ v1_funct_1(E_358) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2741])).

tff(c_3191,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_3173])).

tff(c_3211,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3191])).

tff(c_3348,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3211,c_48])).

tff(c_3354,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_3348])).

tff(c_2500,plain,(
    ! [D_287,C_288,A_289,B_290] :
      ( D_287 = C_288
      | ~ r2_relset_1(A_289,B_290,C_288,D_287)
      | ~ m1_subset_1(D_287,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290)))
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2506,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_2500])).

tff(c_2517,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2506])).

tff(c_2609,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2517])).

tff(c_3425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3354,c_3211,c_2609])).

tff(c_3426,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2517])).

tff(c_3597,plain,(
    ! [E_381,B_386,C_383,D_384,F_385,A_382] :
      ( k1_partfun1(A_382,B_386,C_383,D_384,E_381,F_385) = k5_relat_1(E_381,F_385)
      | ~ m1_subset_1(F_385,k1_zfmisc_1(k2_zfmisc_1(C_383,D_384)))
      | ~ v1_funct_1(F_385)
      | ~ m1_subset_1(E_381,k1_zfmisc_1(k2_zfmisc_1(A_382,B_386)))
      | ~ v1_funct_1(E_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3601,plain,(
    ! [A_382,B_386,E_381] :
      ( k1_partfun1(A_382,B_386,'#skF_2','#skF_1',E_381,'#skF_4') = k5_relat_1(E_381,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_381,k1_zfmisc_1(k2_zfmisc_1(A_382,B_386)))
      | ~ v1_funct_1(E_381) ) ),
    inference(resolution,[status(thm)],[c_68,c_3597])).

tff(c_3799,plain,(
    ! [A_409,B_410,E_411] :
      ( k1_partfun1(A_409,B_410,'#skF_2','#skF_1',E_411,'#skF_4') = k5_relat_1(E_411,'#skF_4')
      | ~ m1_subset_1(E_411,k1_zfmisc_1(k2_zfmisc_1(A_409,B_410)))
      | ~ v1_funct_1(E_411) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3601])).

tff(c_3811,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_3799])).

tff(c_3825,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3426,c_3811])).

tff(c_22,plain,(
    ! [A_9,B_11] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_9,B_11)),k2_relat_1(B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3829,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3825,c_22])).

tff(c_3833,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2089,c_2088,c_80,c_3829])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3837,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3833,c_4])).

tff(c_3838,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3837])).

tff(c_3841,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_3838])).

tff(c_3845,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2088,c_2158,c_3841])).

tff(c_3846,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3837])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2117,plain,(
    ! [B_245,A_246] :
      ( v5_relat_1(B_245,A_246)
      | ~ r1_tarski(k2_relat_1(B_245),A_246)
      | ~ v1_relat_1(B_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2127,plain,(
    ! [B_245] :
      ( v5_relat_1(B_245,k2_relat_1(B_245))
      | ~ v1_relat_1(B_245) ) ),
    inference(resolution,[status(thm)],[c_8,c_2117])).

tff(c_2206,plain,(
    ! [B_265] :
      ( v2_funct_2(B_265,k2_relat_1(B_265))
      | ~ v5_relat_1(B_265,k2_relat_1(B_265))
      | ~ v1_relat_1(B_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2227,plain,(
    ! [B_245] :
      ( v2_funct_2(B_245,k2_relat_1(B_245))
      | ~ v1_relat_1(B_245) ) ),
    inference(resolution,[status(thm)],[c_2127,c_2206])).

tff(c_3853,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3846,c_2227])).

tff(c_3869,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2088,c_3853])).

tff(c_3871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2005,c_3869])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:31:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.26/3.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.35/3.12  
% 8.35/3.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.35/3.12  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.35/3.12  
% 8.35/3.12  %Foreground sorts:
% 8.35/3.12  
% 8.35/3.12  
% 8.35/3.12  %Background operators:
% 8.35/3.12  
% 8.35/3.12  
% 8.35/3.12  %Foreground operators:
% 8.35/3.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.35/3.12  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.35/3.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.35/3.12  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.35/3.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.35/3.12  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.35/3.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.35/3.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.35/3.12  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.35/3.12  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.35/3.12  tff('#skF_2', type, '#skF_2': $i).
% 8.35/3.12  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.35/3.12  tff('#skF_3', type, '#skF_3': $i).
% 8.35/3.12  tff('#skF_1', type, '#skF_1': $i).
% 8.35/3.12  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.35/3.12  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.35/3.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.35/3.12  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.35/3.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.35/3.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.35/3.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.35/3.12  tff('#skF_4', type, '#skF_4': $i).
% 8.35/3.12  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.35/3.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.35/3.12  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.35/3.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.35/3.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.35/3.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.35/3.12  
% 8.35/3.16  tff(f_175, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 8.35/3.16  tff(f_89, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 8.35/3.16  tff(f_133, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.35/3.16  tff(f_65, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 8.35/3.16  tff(f_131, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.35/3.16  tff(f_117, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.35/3.16  tff(f_121, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 8.35/3.16  tff(f_97, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.35/3.16  tff(f_155, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 8.35/3.16  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.35/3.16  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 8.35/3.16  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.35/3.16  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.35/3.16  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.35/3.16  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.35/3.16  tff(f_63, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.35/3.16  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 8.35/3.16  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.35/3.16  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 8.35/3.16  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.35/3.16  tff(c_300, plain, (![C_97, B_98, A_99]: (v1_xboole_0(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(B_98, A_99))) | ~v1_xboole_0(A_99))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.35/3.16  tff(c_317, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_300])).
% 8.35/3.16  tff(c_321, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_317])).
% 8.35/3.16  tff(c_58, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.35/3.16  tff(c_28, plain, (![A_13]: (v2_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.35/3.16  tff(c_79, plain, (![A_13]: (v2_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_28])).
% 8.35/3.16  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.35/3.16  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.35/3.16  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.35/3.16  tff(c_846, plain, (![D_150, B_152, A_148, E_147, F_151, C_149]: (k1_partfun1(A_148, B_152, C_149, D_150, E_147, F_151)=k5_relat_1(E_147, F_151) | ~m1_subset_1(F_151, k1_zfmisc_1(k2_zfmisc_1(C_149, D_150))) | ~v1_funct_1(F_151) | ~m1_subset_1(E_147, k1_zfmisc_1(k2_zfmisc_1(A_148, B_152))) | ~v1_funct_1(E_147))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.35/3.16  tff(c_850, plain, (![A_148, B_152, E_147]: (k1_partfun1(A_148, B_152, '#skF_2', '#skF_1', E_147, '#skF_4')=k5_relat_1(E_147, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_147, k1_zfmisc_1(k2_zfmisc_1(A_148, B_152))) | ~v1_funct_1(E_147))), inference(resolution, [status(thm)], [c_68, c_846])).
% 8.35/3.16  tff(c_1392, plain, (![A_199, B_200, E_201]: (k1_partfun1(A_199, B_200, '#skF_2', '#skF_1', E_201, '#skF_4')=k5_relat_1(E_201, '#skF_4') | ~m1_subset_1(E_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))) | ~v1_funct_1(E_201))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_850])).
% 8.35/3.16  tff(c_1410, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1392])).
% 8.35/3.16  tff(c_1430, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1410])).
% 8.35/3.16  tff(c_48, plain, (![D_37, A_34, F_39, B_35, C_36, E_38]: (m1_subset_1(k1_partfun1(A_34, B_35, C_36, D_37, E_38, F_39), k1_zfmisc_1(k2_zfmisc_1(A_34, D_37))) | ~m1_subset_1(F_39, k1_zfmisc_1(k2_zfmisc_1(C_36, D_37))) | ~v1_funct_1(F_39) | ~m1_subset_1(E_38, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_1(E_38))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.35/3.16  tff(c_1541, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1430, c_48])).
% 8.35/3.16  tff(c_1548, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_1541])).
% 8.35/3.16  tff(c_54, plain, (![A_40]: (m1_subset_1(k6_partfun1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.35/3.16  tff(c_66, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.35/3.16  tff(c_677, plain, (![D_123, C_124, A_125, B_126]: (D_123=C_124 | ~r2_relset_1(A_125, B_126, C_124, D_123) | ~m1_subset_1(D_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.35/3.16  tff(c_683, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_677])).
% 8.35/3.16  tff(c_694, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_683])).
% 8.35/3.16  tff(c_1646, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1548, c_1430, c_1430, c_694])).
% 8.35/3.16  tff(c_64, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.35/3.16  tff(c_109, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 8.35/3.16  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.35/3.16  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.35/3.16  tff(c_62, plain, (![B_49, A_48, D_51, C_50, E_53]: (k1_xboole_0=C_50 | v2_funct_1(D_51) | ~v2_funct_1(k1_partfun1(A_48, B_49, B_49, C_50, D_51, E_53)) | ~m1_subset_1(E_53, k1_zfmisc_1(k2_zfmisc_1(B_49, C_50))) | ~v1_funct_2(E_53, B_49, C_50) | ~v1_funct_1(E_53) | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_2(D_51, A_48, B_49) | ~v1_funct_1(D_51))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.35/3.16  tff(c_1538, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1430, c_62])).
% 8.35/3.16  tff(c_1545, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_70, c_68, c_1538])).
% 8.35/3.16  tff(c_1546, plain, (k1_xboole_0='#skF_1' | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_109, c_1545])).
% 8.35/3.16  tff(c_1550, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1546])).
% 8.35/3.16  tff(c_1652, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1646, c_1550])).
% 8.35/3.16  tff(c_1662, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_1652])).
% 8.35/3.16  tff(c_1663, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1546])).
% 8.35/3.16  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.35/3.16  tff(c_1699, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1663, c_2])).
% 8.35/3.16  tff(c_1701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_321, c_1699])).
% 8.35/3.16  tff(c_1702, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_317])).
% 8.35/3.16  tff(c_1842, plain, (![A_215]: (v1_xboole_0(k6_partfun1(A_215)) | ~v1_xboole_0(A_215))), inference(resolution, [status(thm)], [c_54, c_300])).
% 8.35/3.16  tff(c_10, plain, (![B_4, A_3]: (~v1_xboole_0(B_4) | B_4=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.35/3.16  tff(c_1710, plain, (![A_3]: (A_3='#skF_4' | ~v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_1702, c_10])).
% 8.35/3.16  tff(c_1865, plain, (![A_218]: (k6_partfun1(A_218)='#skF_4' | ~v1_xboole_0(A_218))), inference(resolution, [status(thm)], [c_1842, c_1710])).
% 8.35/3.16  tff(c_1873, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_1702, c_1865])).
% 8.35/3.16  tff(c_1912, plain, (v2_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1873, c_79])).
% 8.35/3.16  tff(c_138, plain, (![B_63, A_64]: (~v1_xboole_0(B_63) | B_63=A_64 | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.35/3.16  tff(c_141, plain, (![A_64]: (k1_xboole_0=A_64 | ~v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_2, c_138])).
% 8.35/3.16  tff(c_1709, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1702, c_141])).
% 8.35/3.16  tff(c_16, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.35/3.16  tff(c_1724, plain, (![B_6]: (k2_zfmisc_1('#skF_4', B_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1709, c_1709, c_16])).
% 8.35/3.16  tff(c_1703, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_317])).
% 8.35/3.16  tff(c_1716, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1703, c_141])).
% 8.35/3.16  tff(c_1732, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1709, c_1716])).
% 8.35/3.16  tff(c_1738, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1732, c_74])).
% 8.35/3.16  tff(c_1805, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1724, c_1738])).
% 8.35/3.16  tff(c_14, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.35/3.16  tff(c_315, plain, (![C_97]: (v1_xboole_0(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_300])).
% 8.35/3.16  tff(c_320, plain, (![C_97]: (v1_xboole_0(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_315])).
% 8.35/3.16  tff(c_1968, plain, (![C_223]: (v1_xboole_0(C_223) | ~m1_subset_1(C_223, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1709, c_320])).
% 8.35/3.16  tff(c_1977, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1805, c_1968])).
% 8.35/3.16  tff(c_1987, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1977, c_1710])).
% 8.35/3.16  tff(c_1996, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1987, c_109])).
% 8.35/3.16  tff(c_2004, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1912, c_1996])).
% 8.35/3.16  tff(c_2005, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 8.35/3.16  tff(c_2073, plain, (![C_236, A_237, B_238]: (v1_relat_1(C_236) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.35/3.16  tff(c_2088, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_2073])).
% 8.35/3.16  tff(c_2140, plain, (![C_253, B_254, A_255]: (v5_relat_1(C_253, B_254) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_255, B_254))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.35/3.16  tff(c_2158, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_2140])).
% 8.35/3.16  tff(c_20, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.35/3.16  tff(c_2089, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_2073])).
% 8.35/3.16  tff(c_26, plain, (![A_12]: (k2_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.35/3.16  tff(c_80, plain, (![A_12]: (k2_relat_1(k6_partfun1(A_12))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_26])).
% 8.35/3.16  tff(c_2737, plain, (![E_312, B_317, D_315, F_316, C_314, A_313]: (k1_partfun1(A_313, B_317, C_314, D_315, E_312, F_316)=k5_relat_1(E_312, F_316) | ~m1_subset_1(F_316, k1_zfmisc_1(k2_zfmisc_1(C_314, D_315))) | ~v1_funct_1(F_316) | ~m1_subset_1(E_312, k1_zfmisc_1(k2_zfmisc_1(A_313, B_317))) | ~v1_funct_1(E_312))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.35/3.16  tff(c_2741, plain, (![A_313, B_317, E_312]: (k1_partfun1(A_313, B_317, '#skF_2', '#skF_1', E_312, '#skF_4')=k5_relat_1(E_312, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_312, k1_zfmisc_1(k2_zfmisc_1(A_313, B_317))) | ~v1_funct_1(E_312))), inference(resolution, [status(thm)], [c_68, c_2737])).
% 8.35/3.16  tff(c_3173, plain, (![A_356, B_357, E_358]: (k1_partfun1(A_356, B_357, '#skF_2', '#skF_1', E_358, '#skF_4')=k5_relat_1(E_358, '#skF_4') | ~m1_subset_1(E_358, k1_zfmisc_1(k2_zfmisc_1(A_356, B_357))) | ~v1_funct_1(E_358))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2741])).
% 8.35/3.16  tff(c_3191, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_3173])).
% 8.35/3.16  tff(c_3211, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3191])).
% 8.35/3.16  tff(c_3348, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3211, c_48])).
% 8.35/3.16  tff(c_3354, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_3348])).
% 8.35/3.16  tff(c_2500, plain, (![D_287, C_288, A_289, B_290]: (D_287=C_288 | ~r2_relset_1(A_289, B_290, C_288, D_287) | ~m1_subset_1(D_287, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))) | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.35/3.16  tff(c_2506, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_2500])).
% 8.35/3.16  tff(c_2517, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2506])).
% 8.35/3.16  tff(c_2609, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2517])).
% 8.35/3.16  tff(c_3425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3354, c_3211, c_2609])).
% 8.35/3.16  tff(c_3426, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2517])).
% 8.35/3.16  tff(c_3597, plain, (![E_381, B_386, C_383, D_384, F_385, A_382]: (k1_partfun1(A_382, B_386, C_383, D_384, E_381, F_385)=k5_relat_1(E_381, F_385) | ~m1_subset_1(F_385, k1_zfmisc_1(k2_zfmisc_1(C_383, D_384))) | ~v1_funct_1(F_385) | ~m1_subset_1(E_381, k1_zfmisc_1(k2_zfmisc_1(A_382, B_386))) | ~v1_funct_1(E_381))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.35/3.16  tff(c_3601, plain, (![A_382, B_386, E_381]: (k1_partfun1(A_382, B_386, '#skF_2', '#skF_1', E_381, '#skF_4')=k5_relat_1(E_381, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_381, k1_zfmisc_1(k2_zfmisc_1(A_382, B_386))) | ~v1_funct_1(E_381))), inference(resolution, [status(thm)], [c_68, c_3597])).
% 8.35/3.16  tff(c_3799, plain, (![A_409, B_410, E_411]: (k1_partfun1(A_409, B_410, '#skF_2', '#skF_1', E_411, '#skF_4')=k5_relat_1(E_411, '#skF_4') | ~m1_subset_1(E_411, k1_zfmisc_1(k2_zfmisc_1(A_409, B_410))) | ~v1_funct_1(E_411))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3601])).
% 8.35/3.16  tff(c_3811, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_3799])).
% 8.35/3.16  tff(c_3825, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3426, c_3811])).
% 8.35/3.16  tff(c_22, plain, (![A_9, B_11]: (r1_tarski(k2_relat_1(k5_relat_1(A_9, B_11)), k2_relat_1(B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.35/3.16  tff(c_3829, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3825, c_22])).
% 8.35/3.16  tff(c_3833, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2089, c_2088, c_80, c_3829])).
% 8.35/3.16  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.35/3.16  tff(c_3837, plain, (k2_relat_1('#skF_4')='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_3833, c_4])).
% 8.35/3.16  tff(c_3838, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_3837])).
% 8.35/3.16  tff(c_3841, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_3838])).
% 8.35/3.16  tff(c_3845, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2088, c_2158, c_3841])).
% 8.35/3.16  tff(c_3846, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_3837])).
% 8.35/3.16  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.35/3.16  tff(c_2117, plain, (![B_245, A_246]: (v5_relat_1(B_245, A_246) | ~r1_tarski(k2_relat_1(B_245), A_246) | ~v1_relat_1(B_245))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.35/3.16  tff(c_2127, plain, (![B_245]: (v5_relat_1(B_245, k2_relat_1(B_245)) | ~v1_relat_1(B_245))), inference(resolution, [status(thm)], [c_8, c_2117])).
% 8.35/3.16  tff(c_2206, plain, (![B_265]: (v2_funct_2(B_265, k2_relat_1(B_265)) | ~v5_relat_1(B_265, k2_relat_1(B_265)) | ~v1_relat_1(B_265))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.35/3.16  tff(c_2227, plain, (![B_245]: (v2_funct_2(B_245, k2_relat_1(B_245)) | ~v1_relat_1(B_245))), inference(resolution, [status(thm)], [c_2127, c_2206])).
% 8.35/3.16  tff(c_3853, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3846, c_2227])).
% 8.35/3.16  tff(c_3869, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2088, c_3853])).
% 8.35/3.16  tff(c_3871, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2005, c_3869])).
% 8.35/3.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.35/3.16  
% 8.35/3.16  Inference rules
% 8.35/3.16  ----------------------
% 8.35/3.16  #Ref     : 0
% 8.35/3.16  #Sup     : 818
% 8.35/3.16  #Fact    : 0
% 8.35/3.16  #Define  : 0
% 8.35/3.16  #Split   : 14
% 8.35/3.16  #Chain   : 0
% 8.35/3.16  #Close   : 0
% 8.35/3.16  
% 8.35/3.16  Ordering : KBO
% 8.35/3.16  
% 8.35/3.16  Simplification rules
% 8.35/3.16  ----------------------
% 8.35/3.16  #Subsume      : 98
% 8.35/3.16  #Demod        : 702
% 8.35/3.16  #Tautology    : 275
% 8.35/3.16  #SimpNegUnit  : 3
% 8.35/3.16  #BackRed      : 89
% 8.35/3.16  
% 8.35/3.16  #Partial instantiations: 0
% 8.35/3.16  #Strategies tried      : 1
% 8.35/3.16  
% 8.35/3.16  Timing (in seconds)
% 8.35/3.16  ----------------------
% 8.35/3.17  Preprocessing        : 0.57
% 8.35/3.17  Parsing              : 0.30
% 8.35/3.17  CNF conversion       : 0.04
% 8.35/3.17  Main loop            : 1.59
% 8.35/3.17  Inferencing          : 0.54
% 8.35/3.17  Reduction            : 0.58
% 8.35/3.17  Demodulation         : 0.43
% 8.35/3.17  BG Simplification    : 0.06
% 8.35/3.17  Subsumption          : 0.27
% 8.35/3.17  Abstraction          : 0.07
% 8.35/3.17  MUC search           : 0.00
% 8.35/3.17  Cooper               : 0.00
% 8.35/3.17  Total                : 2.25
% 8.35/3.17  Index Insertion      : 0.00
% 8.35/3.17  Index Deletion       : 0.00
% 8.35/3.17  Index Matching       : 0.00
% 8.35/3.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
