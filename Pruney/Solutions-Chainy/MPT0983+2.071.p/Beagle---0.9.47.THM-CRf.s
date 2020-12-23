%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:11 EST 2020

% Result     : Theorem 6.05s
% Output     : CNFRefutation 6.12s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 265 expanded)
%              Number of leaves         :   51 ( 114 expanded)
%              Depth                    :    9
%              Number of atoms          :  242 ( 667 expanded)
%              Number of equality atoms :   37 (  78 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_183,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_124,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_122,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_102,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_163,axiom,(
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

tff(f_69,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_68,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_141,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_72,plain,
    ( ~ v2_funct_2('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_133,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( v1_xboole_0(k2_zfmisc_1(A_12,B_13))
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_82,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_436,plain,(
    ! [C_122,B_123,A_124] :
      ( ~ v1_xboole_0(C_122)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(C_122))
      | ~ r2_hidden(A_124,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_450,plain,(
    ! [A_124] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_124,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_82,c_436])).

tff(c_469,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_450])).

tff(c_473,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_469])).

tff(c_86,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_84,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_80,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_78,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_64,plain,(
    ! [A_46] : k6_relat_1(A_46) = k6_partfun1(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_38,plain,(
    ! [A_21] : v2_funct_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_88,plain,(
    ! [A_21] : v2_funct_1(k6_partfun1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_38])).

tff(c_60,plain,(
    ! [E_44,C_42,F_45,A_40,D_43,B_41] :
      ( m1_subset_1(k1_partfun1(A_40,B_41,C_42,D_43,E_44,F_45),k1_zfmisc_1(k2_zfmisc_1(A_40,D_43)))
      | ~ m1_subset_1(F_45,k1_zfmisc_1(k2_zfmisc_1(C_42,D_43)))
      | ~ v1_funct_1(F_45)
      | ~ m1_subset_1(E_44,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_1(E_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_54,plain,(
    ! [A_37] : m1_subset_1(k6_relat_1(A_37),k1_zfmisc_1(k2_zfmisc_1(A_37,A_37))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_87,plain,(
    ! [A_37] : m1_subset_1(k6_partfun1(A_37),k1_zfmisc_1(k2_zfmisc_1(A_37,A_37))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54])).

tff(c_74,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_742,plain,(
    ! [D_149,C_150,A_151,B_152] :
      ( D_149 = C_150
      | ~ r2_relset_1(A_151,B_152,C_150,D_149)
      | ~ m1_subset_1(D_149,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152)))
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_752,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_74,c_742])).

tff(c_771,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_752])).

tff(c_1600,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_771])).

tff(c_2107,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_1600])).

tff(c_2111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_2107])).

tff(c_2112,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_771])).

tff(c_70,plain,(
    ! [D_55,B_53,E_57,A_52,C_54] :
      ( k1_xboole_0 = C_54
      | v2_funct_1(D_55)
      | ~ v2_funct_1(k1_partfun1(A_52,B_53,B_53,C_54,D_55,E_57))
      | ~ m1_subset_1(E_57,k1_zfmisc_1(k2_zfmisc_1(B_53,C_54)))
      | ~ v1_funct_2(E_57,B_53,C_54)
      | ~ v1_funct_1(E_57)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_2(D_55,A_52,B_53)
      | ~ v1_funct_1(D_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2623,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5')
    | ~ v2_funct_1(k6_partfun1('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2112,c_70])).

tff(c_2630,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_88,c_2623])).

tff(c_2631,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_2630])).

tff(c_108,plain,(
    ! [A_64] : k6_relat_1(A_64) = k6_partfun1(A_64) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_34,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_114,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_34])).

tff(c_36,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_89,plain,(
    ! [A_21] : v1_relat_1(k6_partfun1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_36])).

tff(c_125,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_89])).

tff(c_28,plain,(
    ! [B_20] : v5_relat_1(k1_xboole_0,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_221,plain,(
    ! [B_91,A_92] :
      ( r1_tarski(k2_relat_1(B_91),A_92)
      | ~ v5_relat_1(B_91,A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_237,plain,(
    ! [A_92] :
      ( r1_tarski(k1_xboole_0,A_92)
      | ~ v5_relat_1(k1_xboole_0,A_92)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_221])).

tff(c_244,plain,(
    ! [A_93] : r1_tarski(k1_xboole_0,A_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_28,c_237])).

tff(c_136,plain,(
    ! [A_71] :
      ( v1_xboole_0(A_71)
      | r2_hidden('#skF_1'(A_71),A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [B_23,A_22] :
      ( ~ r1_tarski(B_23,A_22)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_143,plain,(
    ! [A_71] :
      ( ~ r1_tarski(A_71,'#skF_1'(A_71))
      | v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_136,c_40])).

tff(c_262,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_244,c_143])).

tff(c_2663,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2631,c_262])).

tff(c_2674,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_473,c_2663])).

tff(c_2677,plain,(
    ! [A_242] : ~ r2_hidden(A_242,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_2687,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_2677])).

tff(c_157,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_2'(A_76,B_77),A_76)
      | r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_166,plain,(
    ! [A_78,B_79] :
      ( ~ v1_xboole_0(A_78)
      | r1_tarski(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_157,c_2])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_173,plain,(
    ! [B_79,A_78] :
      ( B_79 = A_78
      | ~ r1_tarski(B_79,A_78)
      | ~ v1_xboole_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_166,c_12])).

tff(c_260,plain,(
    ! [A_93] :
      ( k1_xboole_0 = A_93
      | ~ v1_xboole_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_244,c_173])).

tff(c_2699,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2687,c_260])).

tff(c_127,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_88])).

tff(c_2712,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2699,c_127])).

tff(c_2722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_2712])).

tff(c_2723,plain,(
    ~ v2_funct_2('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_2763,plain,(
    ! [C_256,A_257,B_258] :
      ( v1_relat_1(C_256)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2781,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_2763])).

tff(c_3121,plain,(
    ! [A_303,B_304,D_305] :
      ( r2_relset_1(A_303,B_304,D_305,D_305)
      | ~ m1_subset_1(D_305,k1_zfmisc_1(k2_zfmisc_1(A_303,B_304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3130,plain,(
    ! [A_37] : r2_relset_1(A_37,A_37,k6_partfun1(A_37),k6_partfun1(A_37)) ),
    inference(resolution,[status(thm)],[c_87,c_3121])).

tff(c_3265,plain,(
    ! [A_313,B_314,C_315] :
      ( k2_relset_1(A_313,B_314,C_315) = k2_relat_1(C_315)
      | ~ m1_subset_1(C_315,k1_zfmisc_1(k2_zfmisc_1(A_313,B_314))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3280,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_3265])).

tff(c_3431,plain,(
    ! [D_324,C_325,A_326,B_327] :
      ( D_324 = C_325
      | ~ r2_relset_1(A_326,B_327,C_325,D_324)
      | ~ m1_subset_1(D_324,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327)))
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3441,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_74,c_3431])).

tff(c_3460,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_3441])).

tff(c_3646,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_3460])).

tff(c_4407,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_3646])).

tff(c_4411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_4407])).

tff(c_4412,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3460])).

tff(c_6012,plain,(
    ! [A_467,B_468,C_469,D_470] :
      ( k2_relset_1(A_467,B_468,C_469) = B_468
      | ~ r2_relset_1(B_468,B_468,k1_partfun1(B_468,A_467,A_467,B_468,D_470,C_469),k6_partfun1(B_468))
      | ~ m1_subset_1(D_470,k1_zfmisc_1(k2_zfmisc_1(B_468,A_467)))
      | ~ v1_funct_2(D_470,B_468,A_467)
      | ~ v1_funct_1(D_470)
      | ~ m1_subset_1(C_469,k1_zfmisc_1(k2_zfmisc_1(A_467,B_468)))
      | ~ v1_funct_2(C_469,A_467,B_468)
      | ~ v1_funct_1(C_469) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_6018,plain,
    ( k2_relset_1('#skF_4','#skF_3','#skF_6') = '#skF_3'
    | ~ r2_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),k6_partfun1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4412,c_6012])).

tff(c_6035,plain,(
    k2_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_86,c_84,c_82,c_3130,c_3280,c_6018])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2919,plain,(
    ! [B_278,A_279] :
      ( v5_relat_1(B_278,A_279)
      | ~ r1_tarski(k2_relat_1(B_278),A_279)
      | ~ v1_relat_1(B_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2938,plain,(
    ! [B_278] :
      ( v5_relat_1(B_278,k2_relat_1(B_278))
      | ~ v1_relat_1(B_278) ) ),
    inference(resolution,[status(thm)],[c_16,c_2919])).

tff(c_3037,plain,(
    ! [B_295] :
      ( v2_funct_2(B_295,k2_relat_1(B_295))
      | ~ v5_relat_1(B_295,k2_relat_1(B_295))
      | ~ v1_relat_1(B_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_3048,plain,(
    ! [B_278] :
      ( v2_funct_2(B_278,k2_relat_1(B_278))
      | ~ v1_relat_1(B_278) ) ),
    inference(resolution,[status(thm)],[c_2938,c_3037])).

tff(c_6046,plain,
    ( v2_funct_2('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6035,c_3048])).

tff(c_6064,plain,(
    v2_funct_2('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2781,c_6046])).

tff(c_6066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2723,c_6064])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:29:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.05/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.12/2.13  
% 6.12/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.12/2.13  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 6.12/2.13  
% 6.12/2.13  %Foreground sorts:
% 6.12/2.13  
% 6.12/2.13  
% 6.12/2.13  %Background operators:
% 6.12/2.13  
% 6.12/2.13  
% 6.12/2.13  %Foreground operators:
% 6.12/2.13  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.12/2.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.12/2.13  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.12/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.12/2.13  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.12/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.12/2.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.12/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.12/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.12/2.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.12/2.13  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.12/2.13  tff('#skF_5', type, '#skF_5': $i).
% 6.12/2.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.12/2.13  tff('#skF_6', type, '#skF_6': $i).
% 6.12/2.13  tff('#skF_3', type, '#skF_3': $i).
% 6.12/2.13  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.12/2.13  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.12/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.12/2.13  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.12/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.12/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.12/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.12/2.13  tff('#skF_4', type, '#skF_4': $i).
% 6.12/2.13  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.12/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.12/2.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.12/2.13  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.12/2.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.12/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.12/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.12/2.13  
% 6.12/2.15  tff(f_183, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 6.12/2.15  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.12/2.15  tff(f_48, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 6.12/2.15  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 6.12/2.15  tff(f_124, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.12/2.15  tff(f_73, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.12/2.15  tff(f_122, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.12/2.15  tff(f_102, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 6.12/2.15  tff(f_100, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.12/2.15  tff(f_163, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 6.12/2.15  tff(f_69, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 6.12/2.15  tff(f_65, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l222_relat_1)).
% 6.12/2.15  tff(f_68, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 6.12/2.15  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 6.12/2.15  tff(f_78, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.12/2.15  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.12/2.15  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.12/2.15  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.12/2.15  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.12/2.15  tff(f_141, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 6.12/2.15  tff(f_110, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.12/2.15  tff(c_72, plain, (~v2_funct_2('#skF_6', '#skF_3') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.12/2.15  tff(c_133, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_72])).
% 6.12/2.15  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.12/2.15  tff(c_18, plain, (![A_12, B_13]: (v1_xboole_0(k2_zfmisc_1(A_12, B_13)) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.12/2.15  tff(c_82, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.12/2.15  tff(c_436, plain, (![C_122, B_123, A_124]: (~v1_xboole_0(C_122) | ~m1_subset_1(B_123, k1_zfmisc_1(C_122)) | ~r2_hidden(A_124, B_123))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.12/2.15  tff(c_450, plain, (![A_124]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_124, '#skF_5'))), inference(resolution, [status(thm)], [c_82, c_436])).
% 6.12/2.15  tff(c_469, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_450])).
% 6.12/2.15  tff(c_473, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_18, c_469])).
% 6.12/2.15  tff(c_86, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.12/2.15  tff(c_84, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.12/2.15  tff(c_80, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.12/2.15  tff(c_78, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.12/2.15  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.12/2.15  tff(c_64, plain, (![A_46]: (k6_relat_1(A_46)=k6_partfun1(A_46))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.12/2.15  tff(c_38, plain, (![A_21]: (v2_funct_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.12/2.15  tff(c_88, plain, (![A_21]: (v2_funct_1(k6_partfun1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_38])).
% 6.12/2.15  tff(c_60, plain, (![E_44, C_42, F_45, A_40, D_43, B_41]: (m1_subset_1(k1_partfun1(A_40, B_41, C_42, D_43, E_44, F_45), k1_zfmisc_1(k2_zfmisc_1(A_40, D_43))) | ~m1_subset_1(F_45, k1_zfmisc_1(k2_zfmisc_1(C_42, D_43))) | ~v1_funct_1(F_45) | ~m1_subset_1(E_44, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_1(E_44))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.12/2.15  tff(c_54, plain, (![A_37]: (m1_subset_1(k6_relat_1(A_37), k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.12/2.15  tff(c_87, plain, (![A_37]: (m1_subset_1(k6_partfun1(A_37), k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54])).
% 6.12/2.15  tff(c_74, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.12/2.15  tff(c_742, plain, (![D_149, C_150, A_151, B_152]: (D_149=C_150 | ~r2_relset_1(A_151, B_152, C_150, D_149) | ~m1_subset_1(D_149, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.12/2.15  tff(c_752, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_74, c_742])).
% 6.12/2.15  tff(c_771, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_752])).
% 6.12/2.15  tff(c_1600, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_771])).
% 6.12/2.15  tff(c_2107, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_1600])).
% 6.12/2.15  tff(c_2111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_2107])).
% 6.12/2.15  tff(c_2112, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_771])).
% 6.12/2.15  tff(c_70, plain, (![D_55, B_53, E_57, A_52, C_54]: (k1_xboole_0=C_54 | v2_funct_1(D_55) | ~v2_funct_1(k1_partfun1(A_52, B_53, B_53, C_54, D_55, E_57)) | ~m1_subset_1(E_57, k1_zfmisc_1(k2_zfmisc_1(B_53, C_54))) | ~v1_funct_2(E_57, B_53, C_54) | ~v1_funct_1(E_57) | ~m1_subset_1(D_55, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~v1_funct_2(D_55, A_52, B_53) | ~v1_funct_1(D_55))), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.12/2.15  tff(c_2623, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5') | ~v2_funct_1(k6_partfun1('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2112, c_70])).
% 6.12/2.15  tff(c_2630, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_78, c_76, c_88, c_2623])).
% 6.12/2.15  tff(c_2631, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_133, c_2630])).
% 6.12/2.15  tff(c_108, plain, (![A_64]: (k6_relat_1(A_64)=k6_partfun1(A_64))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.12/2.15  tff(c_34, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.12/2.15  tff(c_114, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_108, c_34])).
% 6.12/2.15  tff(c_36, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.12/2.15  tff(c_89, plain, (![A_21]: (v1_relat_1(k6_partfun1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_36])).
% 6.12/2.15  tff(c_125, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_114, c_89])).
% 6.12/2.15  tff(c_28, plain, (![B_20]: (v5_relat_1(k1_xboole_0, B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.12/2.15  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.12/2.15  tff(c_221, plain, (![B_91, A_92]: (r1_tarski(k2_relat_1(B_91), A_92) | ~v5_relat_1(B_91, A_92) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.12/2.15  tff(c_237, plain, (![A_92]: (r1_tarski(k1_xboole_0, A_92) | ~v5_relat_1(k1_xboole_0, A_92) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_221])).
% 6.12/2.15  tff(c_244, plain, (![A_93]: (r1_tarski(k1_xboole_0, A_93))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_28, c_237])).
% 6.12/2.15  tff(c_136, plain, (![A_71]: (v1_xboole_0(A_71) | r2_hidden('#skF_1'(A_71), A_71))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.12/2.15  tff(c_40, plain, (![B_23, A_22]: (~r1_tarski(B_23, A_22) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.12/2.15  tff(c_143, plain, (![A_71]: (~r1_tarski(A_71, '#skF_1'(A_71)) | v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_136, c_40])).
% 6.12/2.15  tff(c_262, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_244, c_143])).
% 6.12/2.15  tff(c_2663, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2631, c_262])).
% 6.12/2.15  tff(c_2674, plain, $false, inference(negUnitSimplification, [status(thm)], [c_473, c_2663])).
% 6.12/2.15  tff(c_2677, plain, (![A_242]: (~r2_hidden(A_242, '#skF_5'))), inference(splitRight, [status(thm)], [c_450])).
% 6.12/2.15  tff(c_2687, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_2677])).
% 6.12/2.15  tff(c_157, plain, (![A_76, B_77]: (r2_hidden('#skF_2'(A_76, B_77), A_76) | r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.12/2.15  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.12/2.15  tff(c_166, plain, (![A_78, B_79]: (~v1_xboole_0(A_78) | r1_tarski(A_78, B_79))), inference(resolution, [status(thm)], [c_157, c_2])).
% 6.12/2.15  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.12/2.15  tff(c_173, plain, (![B_79, A_78]: (B_79=A_78 | ~r1_tarski(B_79, A_78) | ~v1_xboole_0(A_78))), inference(resolution, [status(thm)], [c_166, c_12])).
% 6.12/2.15  tff(c_260, plain, (![A_93]: (k1_xboole_0=A_93 | ~v1_xboole_0(A_93))), inference(resolution, [status(thm)], [c_244, c_173])).
% 6.12/2.15  tff(c_2699, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2687, c_260])).
% 6.12/2.15  tff(c_127, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_114, c_88])).
% 6.12/2.15  tff(c_2712, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2699, c_127])).
% 6.12/2.15  tff(c_2722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_2712])).
% 6.12/2.15  tff(c_2723, plain, (~v2_funct_2('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_72])).
% 6.12/2.15  tff(c_2763, plain, (![C_256, A_257, B_258]: (v1_relat_1(C_256) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.12/2.15  tff(c_2781, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_2763])).
% 6.12/2.15  tff(c_3121, plain, (![A_303, B_304, D_305]: (r2_relset_1(A_303, B_304, D_305, D_305) | ~m1_subset_1(D_305, k1_zfmisc_1(k2_zfmisc_1(A_303, B_304))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.12/2.15  tff(c_3130, plain, (![A_37]: (r2_relset_1(A_37, A_37, k6_partfun1(A_37), k6_partfun1(A_37)))), inference(resolution, [status(thm)], [c_87, c_3121])).
% 6.12/2.15  tff(c_3265, plain, (![A_313, B_314, C_315]: (k2_relset_1(A_313, B_314, C_315)=k2_relat_1(C_315) | ~m1_subset_1(C_315, k1_zfmisc_1(k2_zfmisc_1(A_313, B_314))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.12/2.15  tff(c_3280, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_3265])).
% 6.12/2.15  tff(c_3431, plain, (![D_324, C_325, A_326, B_327]: (D_324=C_325 | ~r2_relset_1(A_326, B_327, C_325, D_324) | ~m1_subset_1(D_324, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))) | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.12/2.15  tff(c_3441, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_74, c_3431])).
% 6.12/2.15  tff(c_3460, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_3441])).
% 6.12/2.15  tff(c_3646, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_3460])).
% 6.12/2.15  tff(c_4407, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_3646])).
% 6.12/2.15  tff(c_4411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_4407])).
% 6.12/2.15  tff(c_4412, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_3460])).
% 6.12/2.15  tff(c_6012, plain, (![A_467, B_468, C_469, D_470]: (k2_relset_1(A_467, B_468, C_469)=B_468 | ~r2_relset_1(B_468, B_468, k1_partfun1(B_468, A_467, A_467, B_468, D_470, C_469), k6_partfun1(B_468)) | ~m1_subset_1(D_470, k1_zfmisc_1(k2_zfmisc_1(B_468, A_467))) | ~v1_funct_2(D_470, B_468, A_467) | ~v1_funct_1(D_470) | ~m1_subset_1(C_469, k1_zfmisc_1(k2_zfmisc_1(A_467, B_468))) | ~v1_funct_2(C_469, A_467, B_468) | ~v1_funct_1(C_469))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.12/2.15  tff(c_6018, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_6')='#skF_3' | ~r2_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), k6_partfun1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4412, c_6012])).
% 6.12/2.15  tff(c_6035, plain, (k2_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_86, c_84, c_82, c_3130, c_3280, c_6018])).
% 6.12/2.15  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.12/2.15  tff(c_2919, plain, (![B_278, A_279]: (v5_relat_1(B_278, A_279) | ~r1_tarski(k2_relat_1(B_278), A_279) | ~v1_relat_1(B_278))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.12/2.15  tff(c_2938, plain, (![B_278]: (v5_relat_1(B_278, k2_relat_1(B_278)) | ~v1_relat_1(B_278))), inference(resolution, [status(thm)], [c_16, c_2919])).
% 6.12/2.15  tff(c_3037, plain, (![B_295]: (v2_funct_2(B_295, k2_relat_1(B_295)) | ~v5_relat_1(B_295, k2_relat_1(B_295)) | ~v1_relat_1(B_295))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.12/2.15  tff(c_3048, plain, (![B_278]: (v2_funct_2(B_278, k2_relat_1(B_278)) | ~v1_relat_1(B_278))), inference(resolution, [status(thm)], [c_2938, c_3037])).
% 6.12/2.15  tff(c_6046, plain, (v2_funct_2('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6035, c_3048])).
% 6.12/2.15  tff(c_6064, plain, (v2_funct_2('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2781, c_6046])).
% 6.12/2.15  tff(c_6066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2723, c_6064])).
% 6.12/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.12/2.15  
% 6.12/2.15  Inference rules
% 6.12/2.15  ----------------------
% 6.12/2.15  #Ref     : 0
% 6.12/2.15  #Sup     : 1435
% 6.12/2.15  #Fact    : 0
% 6.12/2.15  #Define  : 0
% 6.12/2.15  #Split   : 10
% 6.12/2.15  #Chain   : 0
% 6.12/2.15  #Close   : 0
% 6.12/2.15  
% 6.12/2.15  Ordering : KBO
% 6.12/2.15  
% 6.12/2.15  Simplification rules
% 6.12/2.15  ----------------------
% 6.12/2.15  #Subsume      : 211
% 6.12/2.15  #Demod        : 1298
% 6.12/2.15  #Tautology    : 718
% 6.12/2.15  #SimpNegUnit  : 5
% 6.12/2.15  #BackRed      : 64
% 6.12/2.15  
% 6.12/2.15  #Partial instantiations: 0
% 6.12/2.15  #Strategies tried      : 1
% 6.12/2.15  
% 6.12/2.15  Timing (in seconds)
% 6.12/2.15  ----------------------
% 6.12/2.15  Preprocessing        : 0.34
% 6.12/2.15  Parsing              : 0.18
% 6.12/2.15  CNF conversion       : 0.03
% 6.12/2.15  Main loop            : 1.04
% 6.12/2.15  Inferencing          : 0.33
% 6.12/2.15  Reduction            : 0.36
% 6.12/2.15  Demodulation         : 0.26
% 6.12/2.15  BG Simplification    : 0.04
% 6.12/2.15  Subsumption          : 0.23
% 6.12/2.15  Abstraction          : 0.05
% 6.12/2.15  MUC search           : 0.00
% 6.12/2.15  Cooper               : 0.00
% 6.12/2.15  Total                : 1.43
% 6.12/2.15  Index Insertion      : 0.00
% 6.12/2.15  Index Deletion       : 0.00
% 6.12/2.15  Index Matching       : 0.00
% 6.12/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
