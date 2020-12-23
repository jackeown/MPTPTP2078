%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:07 EST 2020

% Result     : Theorem 6.66s
% Output     : CNFRefutation 6.66s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 157 expanded)
%              Number of leaves         :   41 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :  166 ( 343 expanded)
%              Number of equality atoms :   46 (  82 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
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

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_49,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_92,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_96,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_92])).

tff(c_12,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_169,plain,(
    ! [C_69,B_70,A_71] :
      ( v5_relat_1(C_69,B_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_173,plain,(
    v5_relat_1('#skF_7',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_169])).

tff(c_32,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k2_relat_1(B_19),A_18)
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [C_48,B_49,A_50] :
      ( r2_hidden(C_48,B_49)
      | ~ r2_hidden(C_48,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_200,plain,(
    ! [A_80,B_81,B_82] :
      ( r2_hidden('#skF_1'(A_80,B_81),B_82)
      | ~ r1_tarski(A_80,B_82)
      | r1_tarski(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_10,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_217,plain,(
    ! [A_83,A_84,B_85] :
      ( A_83 = '#skF_1'(A_84,B_85)
      | ~ r1_tarski(A_84,k1_tarski(A_83))
      | r1_tarski(A_84,B_85) ) ),
    inference(resolution,[status(thm)],[c_200,c_10])).

tff(c_342,plain,(
    ! [A_121,B_122,B_123] :
      ( A_121 = '#skF_1'(k2_relat_1(B_122),B_123)
      | r1_tarski(k2_relat_1(B_122),B_123)
      | ~ v5_relat_1(B_122,k1_tarski(A_121))
      | ~ v1_relat_1(B_122) ) ),
    inference(resolution,[status(thm)],[c_32,c_217])).

tff(c_344,plain,(
    ! [B_123] :
      ( '#skF_1'(k2_relat_1('#skF_7'),B_123) = '#skF_5'
      | r1_tarski(k2_relat_1('#skF_7'),B_123)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_173,c_342])).

tff(c_355,plain,(
    ! [B_127] :
      ( '#skF_1'(k2_relat_1('#skF_7'),B_127) = '#skF_5'
      | r1_tarski(k2_relat_1('#skF_7'),B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_344])).

tff(c_216,plain,(
    ! [A_6,A_80,B_81] :
      ( A_6 = '#skF_1'(A_80,B_81)
      | ~ r1_tarski(A_80,k1_tarski(A_6))
      | r1_tarski(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_200,c_10])).

tff(c_494,plain,(
    ! [A_137,B_138] :
      ( A_137 = '#skF_1'(k2_relat_1('#skF_7'),B_138)
      | r1_tarski(k2_relat_1('#skF_7'),B_138)
      | '#skF_1'(k2_relat_1('#skF_7'),k1_tarski(A_137)) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_355,c_216])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( v5_relat_1(B_19,A_18)
      | ~ r1_tarski(k2_relat_1(B_19),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1263,plain,(
    ! [B_138,A_137] :
      ( v5_relat_1('#skF_7',B_138)
      | ~ v1_relat_1('#skF_7')
      | A_137 = '#skF_1'(k2_relat_1('#skF_7'),B_138)
      | '#skF_1'(k2_relat_1('#skF_7'),k1_tarski(A_137)) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_494,c_30])).

tff(c_1473,plain,(
    ! [B_138,A_137] :
      ( v5_relat_1('#skF_7',B_138)
      | A_137 = '#skF_1'(k2_relat_1('#skF_7'),B_138)
      | '#skF_1'(k2_relat_1('#skF_7'),k1_tarski(A_137)) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1263])).

tff(c_3001,plain,(
    ! [A_3678] :
      ( v5_relat_1('#skF_7',k1_tarski(A_3678))
      | '#skF_1'(k2_relat_1('#skF_7'),k1_tarski(A_3678)) = A_3678
      | A_3678 != '#skF_5' ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1473])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3031,plain,(
    ! [A_3678] :
      ( ~ r2_hidden(A_3678,k1_tarski(A_3678))
      | r1_tarski(k2_relat_1('#skF_7'),k1_tarski(A_3678))
      | v5_relat_1('#skF_7',k1_tarski(A_3678))
      | A_3678 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3001,c_4])).

tff(c_3229,plain,(
    ! [A_3731] :
      ( r1_tarski(k2_relat_1('#skF_7'),k1_tarski(A_3731))
      | v5_relat_1('#skF_7',k1_tarski(A_3731))
      | A_3731 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3031])).

tff(c_3241,plain,(
    ! [A_3731] :
      ( ~ v1_relat_1('#skF_7')
      | v5_relat_1('#skF_7',k1_tarski(A_3731))
      | A_3731 != '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_3229,c_30])).

tff(c_3256,plain,(
    ! [A_3731] :
      ( v5_relat_1('#skF_7',k1_tarski(A_3731))
      | A_3731 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_3241])).

tff(c_97,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_1'(A_46,B_47),A_46)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_106,plain,(
    ! [A_46] : r1_tarski(A_46,A_46) ),
    inference(resolution,[status(thm)],[c_97,c_4])).

tff(c_58,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_117,plain,(
    ! [B_49] :
      ( r2_hidden('#skF_6',B_49)
      | ~ r1_tarski('#skF_4',B_49) ) ),
    inference(resolution,[status(thm)],[c_58,c_108])).

tff(c_64,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_62,plain,(
    v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_232,plain,(
    ! [A_89,B_90,C_91] :
      ( k1_relset_1(A_89,B_90,C_91) = k1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_236,plain,(
    k1_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_232])).

tff(c_312,plain,(
    ! [B_115,A_116,C_117] :
      ( k1_xboole_0 = B_115
      | k1_relset_1(A_116,B_115,C_117) = A_116
      | ~ v1_funct_2(C_117,A_116,B_115)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_315,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | k1_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_312])).

tff(c_318,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_236,c_315])).

tff(c_319,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_318])).

tff(c_260,plain,(
    ! [B_98,A_99] :
      ( r2_hidden(k1_funct_1(B_98,A_99),k2_relat_1(B_98))
      | ~ r2_hidden(A_99,k1_relat_1(B_98))
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3715,plain,(
    ! [B_4212,A_4213,B_4214] :
      ( r2_hidden(k1_funct_1(B_4212,A_4213),B_4214)
      | ~ r1_tarski(k2_relat_1(B_4212),B_4214)
      | ~ r2_hidden(A_4213,k1_relat_1(B_4212))
      | ~ v1_funct_1(B_4212)
      | ~ v1_relat_1(B_4212) ) ),
    inference(resolution,[status(thm)],[c_260,c_2])).

tff(c_4085,plain,(
    ! [B_4531,A_4532,A_4533] :
      ( k1_funct_1(B_4531,A_4532) = A_4533
      | ~ r1_tarski(k2_relat_1(B_4531),k1_tarski(A_4533))
      | ~ r2_hidden(A_4532,k1_relat_1(B_4531))
      | ~ v1_funct_1(B_4531)
      | ~ v1_relat_1(B_4531) ) ),
    inference(resolution,[status(thm)],[c_3715,c_10])).

tff(c_7737,plain,(
    ! [B_8968,A_8969,A_8970] :
      ( k1_funct_1(B_8968,A_8969) = A_8970
      | ~ r2_hidden(A_8969,k1_relat_1(B_8968))
      | ~ v1_funct_1(B_8968)
      | ~ v5_relat_1(B_8968,k1_tarski(A_8970))
      | ~ v1_relat_1(B_8968) ) ),
    inference(resolution,[status(thm)],[c_32,c_4085])).

tff(c_7757,plain,(
    ! [A_8969,A_8970] :
      ( k1_funct_1('#skF_7',A_8969) = A_8970
      | ~ r2_hidden(A_8969,'#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',k1_tarski(A_8970))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_7737])).

tff(c_8245,plain,(
    ! [A_9443,A_9444] :
      ( k1_funct_1('#skF_7',A_9443) = A_9444
      | ~ r2_hidden(A_9443,'#skF_4')
      | ~ v5_relat_1('#skF_7',k1_tarski(A_9444)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_64,c_7757])).

tff(c_8271,plain,(
    ! [A_9444] :
      ( k1_funct_1('#skF_7','#skF_6') = A_9444
      | ~ v5_relat_1('#skF_7',k1_tarski(A_9444))
      | ~ r1_tarski('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_117,c_8245])).

tff(c_8292,plain,(
    ! [A_9523] :
      ( k1_funct_1('#skF_7','#skF_6') = A_9523
      | ~ v5_relat_1('#skF_7',k1_tarski(A_9523)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_8271])).

tff(c_8310,plain,(
    k1_funct_1('#skF_7','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3256,c_8292])).

tff(c_56,plain,(
    k1_funct_1('#skF_7','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_8316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8310,c_56])).

tff(c_8317,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_28,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_tarski(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8356,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8317,c_28])).

tff(c_8364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8356])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:25:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.66/2.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.27  
% 6.66/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.27  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 6.66/2.27  
% 6.66/2.27  %Foreground sorts:
% 6.66/2.27  
% 6.66/2.27  
% 6.66/2.27  %Background operators:
% 6.66/2.27  
% 6.66/2.27  
% 6.66/2.27  %Foreground operators:
% 6.66/2.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.66/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.66/2.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.66/2.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.66/2.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.66/2.27  tff('#skF_7', type, '#skF_7': $i).
% 6.66/2.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.66/2.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.66/2.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.66/2.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.66/2.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.66/2.27  tff('#skF_5', type, '#skF_5': $i).
% 6.66/2.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.66/2.27  tff('#skF_6', type, '#skF_6': $i).
% 6.66/2.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.66/2.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.66/2.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.66/2.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.66/2.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.66/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.66/2.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.66/2.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.66/2.27  tff('#skF_4', type, '#skF_4': $i).
% 6.66/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.66/2.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.66/2.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.66/2.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.66/2.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.66/2.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.66/2.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.66/2.27  
% 6.66/2.29  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.66/2.29  tff(f_106, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 6.66/2.29  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.66/2.29  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 6.66/2.29  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.66/2.29  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 6.66/2.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.66/2.29  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.66/2.29  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.66/2.29  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 6.66/2.29  tff(f_49, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 6.66/2.29  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.66/2.29  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.66/2.29  tff(c_92, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.66/2.29  tff(c_96, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_92])).
% 6.66/2.29  tff(c_12, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.66/2.29  tff(c_169, plain, (![C_69, B_70, A_71]: (v5_relat_1(C_69, B_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.66/2.29  tff(c_173, plain, (v5_relat_1('#skF_7', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_169])).
% 6.66/2.29  tff(c_32, plain, (![B_19, A_18]: (r1_tarski(k2_relat_1(B_19), A_18) | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.66/2.29  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.29  tff(c_108, plain, (![C_48, B_49, A_50]: (r2_hidden(C_48, B_49) | ~r2_hidden(C_48, A_50) | ~r1_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.29  tff(c_200, plain, (![A_80, B_81, B_82]: (r2_hidden('#skF_1'(A_80, B_81), B_82) | ~r1_tarski(A_80, B_82) | r1_tarski(A_80, B_81))), inference(resolution, [status(thm)], [c_6, c_108])).
% 6.66/2.29  tff(c_10, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.66/2.29  tff(c_217, plain, (![A_83, A_84, B_85]: (A_83='#skF_1'(A_84, B_85) | ~r1_tarski(A_84, k1_tarski(A_83)) | r1_tarski(A_84, B_85))), inference(resolution, [status(thm)], [c_200, c_10])).
% 6.66/2.29  tff(c_342, plain, (![A_121, B_122, B_123]: (A_121='#skF_1'(k2_relat_1(B_122), B_123) | r1_tarski(k2_relat_1(B_122), B_123) | ~v5_relat_1(B_122, k1_tarski(A_121)) | ~v1_relat_1(B_122))), inference(resolution, [status(thm)], [c_32, c_217])).
% 6.66/2.29  tff(c_344, plain, (![B_123]: ('#skF_1'(k2_relat_1('#skF_7'), B_123)='#skF_5' | r1_tarski(k2_relat_1('#skF_7'), B_123) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_173, c_342])).
% 6.66/2.29  tff(c_355, plain, (![B_127]: ('#skF_1'(k2_relat_1('#skF_7'), B_127)='#skF_5' | r1_tarski(k2_relat_1('#skF_7'), B_127))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_344])).
% 6.66/2.29  tff(c_216, plain, (![A_6, A_80, B_81]: (A_6='#skF_1'(A_80, B_81) | ~r1_tarski(A_80, k1_tarski(A_6)) | r1_tarski(A_80, B_81))), inference(resolution, [status(thm)], [c_200, c_10])).
% 6.66/2.29  tff(c_494, plain, (![A_137, B_138]: (A_137='#skF_1'(k2_relat_1('#skF_7'), B_138) | r1_tarski(k2_relat_1('#skF_7'), B_138) | '#skF_1'(k2_relat_1('#skF_7'), k1_tarski(A_137))='#skF_5')), inference(resolution, [status(thm)], [c_355, c_216])).
% 6.66/2.29  tff(c_30, plain, (![B_19, A_18]: (v5_relat_1(B_19, A_18) | ~r1_tarski(k2_relat_1(B_19), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.66/2.29  tff(c_1263, plain, (![B_138, A_137]: (v5_relat_1('#skF_7', B_138) | ~v1_relat_1('#skF_7') | A_137='#skF_1'(k2_relat_1('#skF_7'), B_138) | '#skF_1'(k2_relat_1('#skF_7'), k1_tarski(A_137))='#skF_5')), inference(resolution, [status(thm)], [c_494, c_30])).
% 6.66/2.29  tff(c_1473, plain, (![B_138, A_137]: (v5_relat_1('#skF_7', B_138) | A_137='#skF_1'(k2_relat_1('#skF_7'), B_138) | '#skF_1'(k2_relat_1('#skF_7'), k1_tarski(A_137))='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_1263])).
% 6.66/2.29  tff(c_3001, plain, (![A_3678]: (v5_relat_1('#skF_7', k1_tarski(A_3678)) | '#skF_1'(k2_relat_1('#skF_7'), k1_tarski(A_3678))=A_3678 | A_3678!='#skF_5')), inference(factorization, [status(thm), theory('equality')], [c_1473])).
% 6.66/2.29  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.29  tff(c_3031, plain, (![A_3678]: (~r2_hidden(A_3678, k1_tarski(A_3678)) | r1_tarski(k2_relat_1('#skF_7'), k1_tarski(A_3678)) | v5_relat_1('#skF_7', k1_tarski(A_3678)) | A_3678!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3001, c_4])).
% 6.66/2.29  tff(c_3229, plain, (![A_3731]: (r1_tarski(k2_relat_1('#skF_7'), k1_tarski(A_3731)) | v5_relat_1('#skF_7', k1_tarski(A_3731)) | A_3731!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3031])).
% 6.66/2.29  tff(c_3241, plain, (![A_3731]: (~v1_relat_1('#skF_7') | v5_relat_1('#skF_7', k1_tarski(A_3731)) | A_3731!='#skF_5')), inference(resolution, [status(thm)], [c_3229, c_30])).
% 6.66/2.29  tff(c_3256, plain, (![A_3731]: (v5_relat_1('#skF_7', k1_tarski(A_3731)) | A_3731!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_3241])).
% 6.66/2.29  tff(c_97, plain, (![A_46, B_47]: (r2_hidden('#skF_1'(A_46, B_47), A_46) | r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.29  tff(c_106, plain, (![A_46]: (r1_tarski(A_46, A_46))), inference(resolution, [status(thm)], [c_97, c_4])).
% 6.66/2.29  tff(c_58, plain, (r2_hidden('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.66/2.29  tff(c_117, plain, (![B_49]: (r2_hidden('#skF_6', B_49) | ~r1_tarski('#skF_4', B_49))), inference(resolution, [status(thm)], [c_58, c_108])).
% 6.66/2.29  tff(c_64, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.66/2.29  tff(c_62, plain, (v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.66/2.29  tff(c_232, plain, (![A_89, B_90, C_91]: (k1_relset_1(A_89, B_90, C_91)=k1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.66/2.29  tff(c_236, plain, (k1_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_232])).
% 6.66/2.29  tff(c_312, plain, (![B_115, A_116, C_117]: (k1_xboole_0=B_115 | k1_relset_1(A_116, B_115, C_117)=A_116 | ~v1_funct_2(C_117, A_116, B_115) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.66/2.29  tff(c_315, plain, (k1_tarski('#skF_5')=k1_xboole_0 | k1_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_312])).
% 6.66/2.29  tff(c_318, plain, (k1_tarski('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_236, c_315])).
% 6.66/2.29  tff(c_319, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_318])).
% 6.66/2.29  tff(c_260, plain, (![B_98, A_99]: (r2_hidden(k1_funct_1(B_98, A_99), k2_relat_1(B_98)) | ~r2_hidden(A_99, k1_relat_1(B_98)) | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.66/2.29  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.29  tff(c_3715, plain, (![B_4212, A_4213, B_4214]: (r2_hidden(k1_funct_1(B_4212, A_4213), B_4214) | ~r1_tarski(k2_relat_1(B_4212), B_4214) | ~r2_hidden(A_4213, k1_relat_1(B_4212)) | ~v1_funct_1(B_4212) | ~v1_relat_1(B_4212))), inference(resolution, [status(thm)], [c_260, c_2])).
% 6.66/2.29  tff(c_4085, plain, (![B_4531, A_4532, A_4533]: (k1_funct_1(B_4531, A_4532)=A_4533 | ~r1_tarski(k2_relat_1(B_4531), k1_tarski(A_4533)) | ~r2_hidden(A_4532, k1_relat_1(B_4531)) | ~v1_funct_1(B_4531) | ~v1_relat_1(B_4531))), inference(resolution, [status(thm)], [c_3715, c_10])).
% 6.66/2.29  tff(c_7737, plain, (![B_8968, A_8969, A_8970]: (k1_funct_1(B_8968, A_8969)=A_8970 | ~r2_hidden(A_8969, k1_relat_1(B_8968)) | ~v1_funct_1(B_8968) | ~v5_relat_1(B_8968, k1_tarski(A_8970)) | ~v1_relat_1(B_8968))), inference(resolution, [status(thm)], [c_32, c_4085])).
% 6.66/2.29  tff(c_7757, plain, (![A_8969, A_8970]: (k1_funct_1('#skF_7', A_8969)=A_8970 | ~r2_hidden(A_8969, '#skF_4') | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', k1_tarski(A_8970)) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_319, c_7737])).
% 6.66/2.29  tff(c_8245, plain, (![A_9443, A_9444]: (k1_funct_1('#skF_7', A_9443)=A_9444 | ~r2_hidden(A_9443, '#skF_4') | ~v5_relat_1('#skF_7', k1_tarski(A_9444)))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_64, c_7757])).
% 6.66/2.29  tff(c_8271, plain, (![A_9444]: (k1_funct_1('#skF_7', '#skF_6')=A_9444 | ~v5_relat_1('#skF_7', k1_tarski(A_9444)) | ~r1_tarski('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_117, c_8245])).
% 6.66/2.29  tff(c_8292, plain, (![A_9523]: (k1_funct_1('#skF_7', '#skF_6')=A_9523 | ~v5_relat_1('#skF_7', k1_tarski(A_9523)))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_8271])).
% 6.66/2.29  tff(c_8310, plain, (k1_funct_1('#skF_7', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_3256, c_8292])).
% 6.66/2.29  tff(c_56, plain, (k1_funct_1('#skF_7', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.66/2.29  tff(c_8316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8310, c_56])).
% 6.66/2.29  tff(c_8317, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_318])).
% 6.66/2.29  tff(c_28, plain, (![A_17]: (~v1_xboole_0(k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.66/2.29  tff(c_8356, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8317, c_28])).
% 6.66/2.29  tff(c_8364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_8356])).
% 6.66/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.29  
% 6.66/2.29  Inference rules
% 6.66/2.29  ----------------------
% 6.66/2.29  #Ref     : 1
% 6.66/2.29  #Sup     : 1591
% 6.66/2.29  #Fact    : 2
% 6.66/2.29  #Define  : 0
% 6.66/2.29  #Split   : 13
% 6.66/2.29  #Chain   : 0
% 6.66/2.29  #Close   : 0
% 6.66/2.29  
% 6.66/2.29  Ordering : KBO
% 6.66/2.29  
% 6.66/2.29  Simplification rules
% 6.66/2.29  ----------------------
% 6.66/2.29  #Subsume      : 169
% 6.66/2.29  #Demod        : 113
% 6.66/2.29  #Tautology    : 247
% 6.66/2.29  #SimpNegUnit  : 11
% 6.66/2.29  #BackRed      : 9
% 6.66/2.29  
% 6.66/2.29  #Partial instantiations: 6462
% 6.66/2.29  #Strategies tried      : 1
% 6.66/2.29  
% 6.66/2.29  Timing (in seconds)
% 6.66/2.29  ----------------------
% 6.66/2.29  Preprocessing        : 0.32
% 6.66/2.29  Parsing              : 0.16
% 6.66/2.29  CNF conversion       : 0.02
% 6.66/2.29  Main loop            : 1.27
% 6.66/2.29  Inferencing          : 0.46
% 6.66/2.29  Reduction            : 0.34
% 6.66/2.29  Demodulation         : 0.24
% 6.66/2.29  BG Simplification    : 0.06
% 6.66/2.29  Subsumption          : 0.31
% 6.66/2.29  Abstraction          : 0.06
% 6.66/2.29  MUC search           : 0.00
% 6.66/2.29  Cooper               : 0.00
% 6.66/2.29  Total                : 1.63
% 6.66/2.29  Index Insertion      : 0.00
% 6.66/2.29  Index Deletion       : 0.00
% 6.66/2.29  Index Matching       : 0.00
% 6.66/2.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
