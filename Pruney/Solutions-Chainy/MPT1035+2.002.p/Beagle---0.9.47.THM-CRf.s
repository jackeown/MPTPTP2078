%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:58 EST 2020

% Result     : Theorem 7.47s
% Output     : CNFRefutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 949 expanded)
%              Number of leaves         :   33 ( 308 expanded)
%              Depth                    :   17
%              Number of atoms          :  374 (3052 expanded)
%              Number of equality atoms :   80 ( 955 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ( B = k1_xboole_0
               => A = k1_xboole_0 )
             => ( r1_partfun1(C,D)
              <=> ! [E] :
                    ( r2_hidden(E,k1_relset_1(A,B,C))
                   => k1_funct_1(C,E) = k1_funct_1(D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_77,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
           => ( r1_partfun1(A,B)
            <=> ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_56,plain,
    ( r2_hidden('#skF_7',k1_relset_1('#skF_3','#skF_4','#skF_5'))
    | ~ r1_partfun1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_69,plain,(
    ~ r1_partfun1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_70,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_70])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_77,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_70])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_143,plain,(
    ! [A_66,B_67,C_68] :
      ( k1_relset_1(A_66,B_67,C_68) = k1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_151,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_143])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] :
      ( m1_subset_1(k1_relset_1(A_16,B_17,C_18),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_176,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_20])).

tff(c_180,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_176])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_121,plain,(
    ! [C_59,A_60,B_61] :
      ( r2_hidden(C_59,A_60)
      | ~ r2_hidden(C_59,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_195,plain,(
    ! [A_73,B_74,A_75] :
      ( r2_hidden('#skF_1'(A_73,B_74),A_75)
      | ~ m1_subset_1(A_73,k1_zfmisc_1(A_75))
      | r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_6,c_121])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_212,plain,(
    ! [A_76,A_77] :
      ( ~ m1_subset_1(A_76,k1_zfmisc_1(A_77))
      | r1_tarski(A_76,A_77) ) ),
    inference(resolution,[status(thm)],[c_195,c_4])).

tff(c_228,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_180,c_212])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_42,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_46,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_150,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_143])).

tff(c_443,plain,(
    ! [B_111,A_112,C_113] :
      ( k1_xboole_0 = B_111
      | k1_relset_1(A_112,B_111,C_113) = A_112
      | ~ v1_funct_2(C_113,A_112,B_111)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_112,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_450,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_443])).

tff(c_457,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_150,c_450])).

tff(c_458,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_457])).

tff(c_166,plain,
    ( m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_20])).

tff(c_170,plain,(
    m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_166])).

tff(c_229,plain,(
    r1_tarski(k1_relat_1('#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_170,c_212])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_244,plain,
    ( k1_relat_1('#skF_6') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_229,c_8])).

tff(c_252,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_464,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_252])).

tff(c_470,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_464])).

tff(c_471,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_961,plain,(
    ! [A_185,B_186] :
      ( r2_hidden('#skF_2'(A_185,B_186),k1_relat_1(A_185))
      | r1_partfun1(A_185,B_186)
      | ~ r1_tarski(k1_relat_1(A_185),k1_relat_1(B_186))
      | ~ v1_funct_1(B_186)
      | ~ v1_relat_1(B_186)
      | ~ v1_funct_1(A_185)
      | ~ v1_relat_1(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_64,plain,(
    ! [E_42] :
      ( r1_partfun1('#skF_5','#skF_6')
      | k1_funct_1('#skF_5',E_42) = k1_funct_1('#skF_6',E_42)
      | ~ r2_hidden(E_42,k1_relset_1('#skF_3','#skF_4','#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_110,plain,(
    ! [E_42] :
      ( k1_funct_1('#skF_5',E_42) = k1_funct_1('#skF_6',E_42)
      | ~ r2_hidden(E_42,k1_relset_1('#skF_3','#skF_4','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_64])).

tff(c_172,plain,(
    ! [E_42] :
      ( k1_funct_1('#skF_5',E_42) = k1_funct_1('#skF_6',E_42)
      | ~ r2_hidden(E_42,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_110])).

tff(c_965,plain,(
    ! [B_186] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',B_186)) = k1_funct_1('#skF_6','#skF_2'('#skF_5',B_186))
      | r1_partfun1('#skF_5',B_186)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_186))
      | ~ v1_funct_1(B_186)
      | ~ v1_relat_1(B_186)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_961,c_172])).

tff(c_2502,plain,(
    ! [B_400] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',B_400)) = k1_funct_1('#skF_6','#skF_2'('#skF_5',B_400))
      | r1_partfun1('#skF_5',B_400)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_400))
      | ~ v1_funct_1(B_400)
      | ~ v1_relat_1(B_400) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_52,c_965])).

tff(c_2511,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_5','#skF_6'))
    | r1_partfun1('#skF_5','#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_2502])).

tff(c_2519,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_5','#skF_6'))
    | r1_partfun1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_48,c_228,c_2511])).

tff(c_2520,plain,(
    k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_2519])).

tff(c_38,plain,(
    ! [B_31,A_25] :
      ( k1_funct_1(B_31,'#skF_2'(A_25,B_31)) != k1_funct_1(A_25,'#skF_2'(A_25,B_31))
      | r1_partfun1(A_25,B_31)
      | ~ r1_tarski(k1_relat_1(A_25),k1_relat_1(B_31))
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2526,plain,
    ( r1_partfun1('#skF_5','#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2520,c_38])).

tff(c_2531,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_52,c_77,c_48,c_228,c_471,c_2526])).

tff(c_2533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_2531])).

tff(c_2535,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,
    ( k1_funct_1('#skF_5','#skF_7') != k1_funct_1('#skF_6','#skF_7')
    | ~ r1_partfun1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2537,plain,(
    k1_funct_1('#skF_5','#skF_7') != k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2535,c_54])).

tff(c_2569,plain,(
    ! [C_408,A_409,B_410] :
      ( v1_relat_1(C_408)
      | ~ m1_subset_1(C_408,k1_zfmisc_1(k2_zfmisc_1(A_409,B_410))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2576,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_2569])).

tff(c_2614,plain,(
    ! [A_423,B_424,C_425] :
      ( k1_relset_1(A_423,B_424,C_425) = k1_relat_1(C_425)
      | ~ m1_subset_1(C_425,k1_zfmisc_1(k2_zfmisc_1(A_423,B_424))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2622,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_2614])).

tff(c_2663,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2622,c_20])).

tff(c_2667,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2663])).

tff(c_2593,plain,(
    ! [C_415,A_416,B_417] :
      ( r2_hidden(C_415,A_416)
      | ~ r2_hidden(C_415,B_417)
      | ~ m1_subset_1(B_417,k1_zfmisc_1(A_416)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2742,plain,(
    ! [A_441,B_442,A_443] :
      ( r2_hidden('#skF_1'(A_441,B_442),A_443)
      | ~ m1_subset_1(A_441,k1_zfmisc_1(A_443))
      | r1_tarski(A_441,B_442) ) ),
    inference(resolution,[status(thm)],[c_6,c_2593])).

tff(c_2754,plain,(
    ! [A_444,A_445] :
      ( ~ m1_subset_1(A_444,k1_zfmisc_1(A_445))
      | r1_tarski(A_444,A_445) ) ),
    inference(resolution,[status(thm)],[c_2742,c_4])).

tff(c_2770,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2667,c_2754])).

tff(c_2621,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_2614])).

tff(c_2816,plain,(
    ! [B_448,A_449,C_450] :
      ( k1_xboole_0 = B_448
      | k1_relset_1(A_449,B_448,C_450) = A_449
      | ~ v1_funct_2(C_450,A_449,B_448)
      | ~ m1_subset_1(C_450,k1_zfmisc_1(k2_zfmisc_1(A_449,B_448))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2823,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_2816])).

tff(c_2830,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2621,c_2823])).

tff(c_2831,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2830])).

tff(c_2650,plain,
    ( m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2621,c_20])).

tff(c_2654,plain,(
    m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2650])).

tff(c_2771,plain,(
    r1_tarski(k1_relat_1('#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2654,c_2754])).

tff(c_2793,plain,
    ( k1_relat_1('#skF_6') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_2771,c_8])).

tff(c_2812,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2793])).

tff(c_2835,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2831,c_2812])).

tff(c_2841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2835])).

tff(c_2842,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2793])).

tff(c_2577,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_2569])).

tff(c_2534,plain,(
    r2_hidden('#skF_7',k1_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2659,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2622,c_2534])).

tff(c_3135,plain,(
    ! [B_488,C_489,A_490] :
      ( k1_funct_1(B_488,C_489) = k1_funct_1(A_490,C_489)
      | ~ r2_hidden(C_489,k1_relat_1(A_490))
      | ~ r1_partfun1(A_490,B_488)
      | ~ r1_tarski(k1_relat_1(A_490),k1_relat_1(B_488))
      | ~ v1_funct_1(B_488)
      | ~ v1_relat_1(B_488)
      | ~ v1_funct_1(A_490)
      | ~ v1_relat_1(A_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3150,plain,(
    ! [B_488] :
      ( k1_funct_1(B_488,'#skF_7') = k1_funct_1('#skF_5','#skF_7')
      | ~ r1_partfun1('#skF_5',B_488)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_488))
      | ~ v1_funct_1(B_488)
      | ~ v1_relat_1(B_488)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2659,c_3135])).

tff(c_3867,plain,(
    ! [B_605] :
      ( k1_funct_1(B_605,'#skF_7') = k1_funct_1('#skF_5','#skF_7')
      | ~ r1_partfun1('#skF_5',B_605)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_605))
      | ~ v1_funct_1(B_605)
      | ~ v1_relat_1(B_605) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2577,c_52,c_3150])).

tff(c_3870,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_6','#skF_7')
    | ~ r1_partfun1('#skF_5','#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2842,c_3867])).

tff(c_3876,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2576,c_48,c_2770,c_2535,c_3870])).

tff(c_3878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2537,c_3876])).

tff(c_3880,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_3879,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_3886,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3880,c_3879])).

tff(c_3940,plain,
    ( r2_hidden('#skF_7',k1_relset_1('#skF_4','#skF_4','#skF_5'))
    | ~ r1_partfun1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3886,c_56])).

tff(c_3941,plain,(
    ~ r1_partfun1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3940])).

tff(c_3898,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3886,c_44])).

tff(c_3931,plain,(
    ! [C_614,A_615,B_616] :
      ( v1_relat_1(C_614)
      | ~ m1_subset_1(C_614,k1_zfmisc_1(k2_zfmisc_1(A_615,B_616))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3939,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3898,c_3931])).

tff(c_3899,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3886,c_50])).

tff(c_3938,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3899,c_3931])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3881,plain,(
    ! [A_8] : r1_tarski('#skF_3',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3879,c_14])).

tff(c_3896,plain,(
    ! [A_8] : r1_tarski('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3886,c_3881])).

tff(c_3962,plain,(
    ! [A_626,B_627,C_628] :
      ( k1_relset_1(A_626,B_627,C_628) = k1_relat_1(C_628)
      | ~ m1_subset_1(C_628,k1_zfmisc_1(k2_zfmisc_1(A_626,B_627))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3969,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3899,c_3962])).

tff(c_4028,plain,(
    ! [A_636,B_637,C_638] :
      ( m1_subset_1(k1_relset_1(A_636,B_637,C_638),k1_zfmisc_1(A_636))
      | ~ m1_subset_1(C_638,k1_zfmisc_1(k2_zfmisc_1(A_636,B_637))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4045,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3969,c_4028])).

tff(c_4052,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3899,c_4045])).

tff(c_3946,plain,(
    ! [C_620,A_621,B_622] :
      ( r2_hidden(C_620,A_621)
      | ~ r2_hidden(C_620,B_622)
      | ~ m1_subset_1(B_622,k1_zfmisc_1(A_621)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3981,plain,(
    ! [A_630,B_631,A_632] :
      ( r2_hidden('#skF_1'(A_630,B_631),A_632)
      | ~ m1_subset_1(A_630,k1_zfmisc_1(A_632))
      | r1_tarski(A_630,B_631) ) ),
    inference(resolution,[status(thm)],[c_6,c_3946])).

tff(c_3992,plain,(
    ! [A_630,A_632] :
      ( ~ m1_subset_1(A_630,k1_zfmisc_1(A_632))
      | r1_tarski(A_630,A_632) ) ),
    inference(resolution,[status(thm)],[c_3981,c_4])).

tff(c_4084,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4052,c_3992])).

tff(c_3908,plain,(
    ! [B_611,A_612] :
      ( B_611 = A_612
      | ~ r1_tarski(B_611,A_612)
      | ~ r1_tarski(A_612,B_611) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3913,plain,(
    ! [A_8] :
      ( A_8 = '#skF_4'
      | ~ r1_tarski(A_8,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3896,c_3908])).

tff(c_4090,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4084,c_3913])).

tff(c_4751,plain,(
    ! [A_724,B_725] :
      ( r2_hidden('#skF_2'(A_724,B_725),k1_relat_1(A_724))
      | r1_partfun1(A_724,B_725)
      | ~ r1_tarski(k1_relat_1(A_724),k1_relat_1(B_725))
      | ~ v1_funct_1(B_725)
      | ~ v1_relat_1(B_725)
      | ~ v1_funct_1(A_724)
      | ~ v1_relat_1(A_724) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4758,plain,(
    ! [B_725] :
      ( r2_hidden('#skF_2'('#skF_5',B_725),'#skF_4')
      | r1_partfun1('#skF_5',B_725)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_725))
      | ~ v1_funct_1(B_725)
      | ~ v1_relat_1(B_725)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4090,c_4751])).

tff(c_4768,plain,(
    ! [B_726] :
      ( r2_hidden('#skF_2'('#skF_5',B_726),'#skF_4')
      | r1_partfun1('#skF_5',B_726)
      | ~ v1_funct_1(B_726)
      | ~ v1_relat_1(B_726) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3938,c_52,c_3896,c_4090,c_4758])).

tff(c_4002,plain,(
    ! [E_42] :
      ( r1_partfun1('#skF_5','#skF_6')
      | k1_funct_1('#skF_5',E_42) = k1_funct_1('#skF_6',E_42)
      | ~ r2_hidden(E_42,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3969,c_3886,c_64])).

tff(c_4003,plain,(
    ! [E_42] :
      ( k1_funct_1('#skF_5',E_42) = k1_funct_1('#skF_6',E_42)
      | ~ r2_hidden(E_42,k1_relat_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3941,c_4002])).

tff(c_4096,plain,(
    ! [E_42] :
      ( k1_funct_1('#skF_5',E_42) = k1_funct_1('#skF_6',E_42)
      | ~ r2_hidden(E_42,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4090,c_4003])).

tff(c_5145,plain,(
    ! [B_774] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',B_774)) = k1_funct_1('#skF_6','#skF_2'('#skF_5',B_774))
      | r1_partfun1('#skF_5',B_774)
      | ~ v1_funct_1(B_774)
      | ~ v1_relat_1(B_774) ) ),
    inference(resolution,[status(thm)],[c_4768,c_4096])).

tff(c_5150,plain,(
    ! [B_774] :
      ( k1_funct_1(B_774,'#skF_2'('#skF_5',B_774)) != k1_funct_1('#skF_6','#skF_2'('#skF_5',B_774))
      | r1_partfun1('#skF_5',B_774)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_774))
      | ~ v1_funct_1(B_774)
      | ~ v1_relat_1(B_774)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | r1_partfun1('#skF_5',B_774)
      | ~ v1_funct_1(B_774)
      | ~ v1_relat_1(B_774) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5145,c_38])).

tff(c_5156,plain,(
    ! [B_774] :
      ( k1_funct_1(B_774,'#skF_2'('#skF_5',B_774)) != k1_funct_1('#skF_6','#skF_2'('#skF_5',B_774))
      | r1_partfun1('#skF_5',B_774)
      | ~ v1_funct_1(B_774)
      | ~ v1_relat_1(B_774) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3938,c_52,c_3896,c_4090,c_5150])).

tff(c_5166,plain,
    ( r1_partfun1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5156])).

tff(c_5168,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3939,c_48,c_5166])).

tff(c_5170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3941,c_5168])).

tff(c_5172,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_3940])).

tff(c_5174,plain,(
    k1_funct_1('#skF_5','#skF_7') != k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5172,c_54])).

tff(c_5210,plain,(
    ! [A_786,B_787,C_788] :
      ( k1_relset_1(A_786,B_787,C_788) = k1_relat_1(C_788)
      | ~ m1_subset_1(C_788,k1_zfmisc_1(k2_zfmisc_1(A_786,B_787))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5217,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3899,c_5210])).

tff(c_5247,plain,(
    ! [A_792,B_793,C_794] :
      ( m1_subset_1(k1_relset_1(A_792,B_793,C_794),k1_zfmisc_1(A_792))
      | ~ m1_subset_1(C_794,k1_zfmisc_1(k2_zfmisc_1(A_792,B_793))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5261,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5217,c_5247])).

tff(c_5267,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3899,c_5261])).

tff(c_5171,plain,(
    r2_hidden('#skF_7',k1_relset_1('#skF_4','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3940])).

tff(c_5190,plain,(
    ! [C_779,A_780,B_781] :
      ( r2_hidden(C_779,A_780)
      | ~ r2_hidden(C_779,B_781)
      | ~ m1_subset_1(B_781,k1_zfmisc_1(A_780)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5195,plain,(
    ! [A_780] :
      ( r2_hidden('#skF_7',A_780)
      | ~ m1_subset_1(k1_relset_1('#skF_4','#skF_4','#skF_5'),k1_zfmisc_1(A_780)) ) ),
    inference(resolution,[status(thm)],[c_5171,c_5190])).

tff(c_5219,plain,(
    ! [A_780] :
      ( r2_hidden('#skF_7',A_780)
      | ~ m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1(A_780)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5217,c_5195])).

tff(c_5271,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_5267,c_5219])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5275,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_7',B_2)
      | ~ r1_tarski('#skF_4',B_2) ) ),
    inference(resolution,[status(thm)],[c_5271,c_2])).

tff(c_5279,plain,(
    ! [B_2] : r2_hidden('#skF_7',B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3896,c_5275])).

tff(c_5295,plain,(
    ! [A_796,B_797,A_798] :
      ( r2_hidden('#skF_1'(A_796,B_797),A_798)
      | ~ m1_subset_1(A_796,k1_zfmisc_1(A_798))
      | r1_tarski(A_796,B_797) ) ),
    inference(resolution,[status(thm)],[c_6,c_5190])).

tff(c_5307,plain,(
    ! [A_799,A_800] :
      ( ~ m1_subset_1(A_799,k1_zfmisc_1(A_800))
      | r1_tarski(A_799,A_800) ) ),
    inference(resolution,[status(thm)],[c_5295,c_4])).

tff(c_5323,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_5267,c_5307])).

tff(c_5333,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5323,c_3913])).

tff(c_6115,plain,(
    ! [B_914,C_915,A_916] :
      ( k1_funct_1(B_914,C_915) = k1_funct_1(A_916,C_915)
      | ~ r2_hidden(C_915,k1_relat_1(A_916))
      | ~ r1_partfun1(A_916,B_914)
      | ~ r1_tarski(k1_relat_1(A_916),k1_relat_1(B_914))
      | ~ v1_funct_1(B_914)
      | ~ v1_relat_1(B_914)
      | ~ v1_funct_1(A_916)
      | ~ v1_relat_1(A_916) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6139,plain,(
    ! [B_914,C_915] :
      ( k1_funct_1(B_914,C_915) = k1_funct_1('#skF_5',C_915)
      | ~ r2_hidden(C_915,'#skF_4')
      | ~ r1_partfun1('#skF_5',B_914)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_914))
      | ~ v1_funct_1(B_914)
      | ~ v1_relat_1(B_914)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5333,c_6115])).

tff(c_6218,plain,(
    ! [B_920,C_921] :
      ( k1_funct_1(B_920,C_921) = k1_funct_1('#skF_5',C_921)
      | ~ r2_hidden(C_921,'#skF_4')
      | ~ r1_partfun1('#skF_5',B_920)
      | ~ v1_funct_1(B_920)
      | ~ v1_relat_1(B_920) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3938,c_52,c_3896,c_5333,c_6139])).

tff(c_6261,plain,(
    ! [B_922] :
      ( k1_funct_1(B_922,'#skF_7') = k1_funct_1('#skF_5','#skF_7')
      | ~ r1_partfun1('#skF_5',B_922)
      | ~ v1_funct_1(B_922)
      | ~ v1_relat_1(B_922) ) ),
    inference(resolution,[status(thm)],[c_5279,c_6218])).

tff(c_6268,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_5172,c_6261])).

tff(c_6275,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3939,c_48,c_6268])).

tff(c_6277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5174,c_6275])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.47/2.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.47/2.59  
% 7.47/2.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.69/2.59  %$ v1_funct_2 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 7.69/2.59  
% 7.69/2.59  %Foreground sorts:
% 7.69/2.59  
% 7.69/2.59  
% 7.69/2.59  %Background operators:
% 7.69/2.59  
% 7.69/2.59  
% 7.69/2.59  %Foreground operators:
% 7.69/2.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.69/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.69/2.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.69/2.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.69/2.59  tff('#skF_7', type, '#skF_7': $i).
% 7.69/2.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.69/2.59  tff('#skF_5', type, '#skF_5': $i).
% 7.69/2.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.69/2.59  tff('#skF_6', type, '#skF_6': $i).
% 7.69/2.59  tff('#skF_3', type, '#skF_3': $i).
% 7.69/2.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.69/2.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.69/2.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.69/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.69/2.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.69/2.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.69/2.59  tff('#skF_4', type, '#skF_4': $i).
% 7.69/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.69/2.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.69/2.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.69/2.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.69/2.59  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 7.69/2.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.69/2.59  
% 7.69/2.62  tff(f_118, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (r1_partfun1(C, D) <=> (![E]: (r2_hidden(E, k1_relset_1(A, B, C)) => (k1_funct_1(C, E) = k1_funct_1(D, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_2)).
% 7.69/2.62  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.69/2.62  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.69/2.62  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 7.69/2.62  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.69/2.62  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 7.69/2.62  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.69/2.62  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.69/2.62  tff(f_95, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) => (r1_partfun1(A, B) <=> (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_partfun1)).
% 7.69/2.62  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.69/2.62  tff(c_56, plain, (r2_hidden('#skF_7', k1_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~r1_partfun1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.69/2.62  tff(c_69, plain, (~r1_partfun1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_56])).
% 7.69/2.62  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.69/2.62  tff(c_70, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.69/2.62  tff(c_78, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_70])).
% 7.69/2.62  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.69/2.62  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.69/2.62  tff(c_77, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_70])).
% 7.69/2.62  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.69/2.62  tff(c_143, plain, (![A_66, B_67, C_68]: (k1_relset_1(A_66, B_67, C_68)=k1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.69/2.62  tff(c_151, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_143])).
% 7.69/2.62  tff(c_20, plain, (![A_16, B_17, C_18]: (m1_subset_1(k1_relset_1(A_16, B_17, C_18), k1_zfmisc_1(A_16)) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.69/2.62  tff(c_176, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_151, c_20])).
% 7.69/2.62  tff(c_180, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_176])).
% 7.69/2.62  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.69/2.62  tff(c_121, plain, (![C_59, A_60, B_61]: (r2_hidden(C_59, A_60) | ~r2_hidden(C_59, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.69/2.62  tff(c_195, plain, (![A_73, B_74, A_75]: (r2_hidden('#skF_1'(A_73, B_74), A_75) | ~m1_subset_1(A_73, k1_zfmisc_1(A_75)) | r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_6, c_121])).
% 7.69/2.62  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.69/2.62  tff(c_212, plain, (![A_76, A_77]: (~m1_subset_1(A_76, k1_zfmisc_1(A_77)) | r1_tarski(A_76, A_77))), inference(resolution, [status(thm)], [c_195, c_4])).
% 7.69/2.62  tff(c_228, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_180, c_212])).
% 7.69/2.62  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.69/2.62  tff(c_42, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.69/2.62  tff(c_68, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_42])).
% 7.69/2.62  tff(c_46, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.69/2.62  tff(c_150, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_143])).
% 7.69/2.62  tff(c_443, plain, (![B_111, A_112, C_113]: (k1_xboole_0=B_111 | k1_relset_1(A_112, B_111, C_113)=A_112 | ~v1_funct_2(C_113, A_112, B_111) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_112, B_111))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.69/2.62  tff(c_450, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_443])).
% 7.69/2.62  tff(c_457, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_150, c_450])).
% 7.69/2.62  tff(c_458, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_68, c_457])).
% 7.69/2.62  tff(c_166, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_150, c_20])).
% 7.69/2.62  tff(c_170, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_166])).
% 7.69/2.62  tff(c_229, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_170, c_212])).
% 7.69/2.62  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.69/2.62  tff(c_244, plain, (k1_relat_1('#skF_6')='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_229, c_8])).
% 7.69/2.62  tff(c_252, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_244])).
% 7.69/2.62  tff(c_464, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_458, c_252])).
% 7.69/2.62  tff(c_470, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_464])).
% 7.69/2.62  tff(c_471, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitRight, [status(thm)], [c_244])).
% 7.69/2.62  tff(c_961, plain, (![A_185, B_186]: (r2_hidden('#skF_2'(A_185, B_186), k1_relat_1(A_185)) | r1_partfun1(A_185, B_186) | ~r1_tarski(k1_relat_1(A_185), k1_relat_1(B_186)) | ~v1_funct_1(B_186) | ~v1_relat_1(B_186) | ~v1_funct_1(A_185) | ~v1_relat_1(A_185))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.69/2.62  tff(c_64, plain, (![E_42]: (r1_partfun1('#skF_5', '#skF_6') | k1_funct_1('#skF_5', E_42)=k1_funct_1('#skF_6', E_42) | ~r2_hidden(E_42, k1_relset_1('#skF_3', '#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.69/2.62  tff(c_110, plain, (![E_42]: (k1_funct_1('#skF_5', E_42)=k1_funct_1('#skF_6', E_42) | ~r2_hidden(E_42, k1_relset_1('#skF_3', '#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_69, c_64])).
% 7.69/2.62  tff(c_172, plain, (![E_42]: (k1_funct_1('#skF_5', E_42)=k1_funct_1('#skF_6', E_42) | ~r2_hidden(E_42, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_110])).
% 7.69/2.62  tff(c_965, plain, (![B_186]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_186))=k1_funct_1('#skF_6', '#skF_2'('#skF_5', B_186)) | r1_partfun1('#skF_5', B_186) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_186)) | ~v1_funct_1(B_186) | ~v1_relat_1(B_186) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_961, c_172])).
% 7.69/2.62  tff(c_2502, plain, (![B_400]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_400))=k1_funct_1('#skF_6', '#skF_2'('#skF_5', B_400)) | r1_partfun1('#skF_5', B_400) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_400)) | ~v1_funct_1(B_400) | ~v1_relat_1(B_400))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_52, c_965])).
% 7.69/2.62  tff(c_2511, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_5', '#skF_6')) | r1_partfun1('#skF_5', '#skF_6') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_471, c_2502])).
% 7.69/2.62  tff(c_2519, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_5', '#skF_6')) | r1_partfun1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_48, c_228, c_2511])).
% 7.69/2.62  tff(c_2520, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_69, c_2519])).
% 7.69/2.62  tff(c_38, plain, (![B_31, A_25]: (k1_funct_1(B_31, '#skF_2'(A_25, B_31))!=k1_funct_1(A_25, '#skF_2'(A_25, B_31)) | r1_partfun1(A_25, B_31) | ~r1_tarski(k1_relat_1(A_25), k1_relat_1(B_31)) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.69/2.62  tff(c_2526, plain, (r1_partfun1('#skF_5', '#skF_6') | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2520, c_38])).
% 7.69/2.62  tff(c_2531, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_52, c_77, c_48, c_228, c_471, c_2526])).
% 7.69/2.62  tff(c_2533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_2531])).
% 7.69/2.62  tff(c_2535, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_56])).
% 7.69/2.62  tff(c_54, plain, (k1_funct_1('#skF_5', '#skF_7')!=k1_funct_1('#skF_6', '#skF_7') | ~r1_partfun1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.69/2.62  tff(c_2537, plain, (k1_funct_1('#skF_5', '#skF_7')!=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2535, c_54])).
% 7.69/2.62  tff(c_2569, plain, (![C_408, A_409, B_410]: (v1_relat_1(C_408) | ~m1_subset_1(C_408, k1_zfmisc_1(k2_zfmisc_1(A_409, B_410))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.69/2.62  tff(c_2576, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_2569])).
% 7.69/2.62  tff(c_2614, plain, (![A_423, B_424, C_425]: (k1_relset_1(A_423, B_424, C_425)=k1_relat_1(C_425) | ~m1_subset_1(C_425, k1_zfmisc_1(k2_zfmisc_1(A_423, B_424))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.69/2.62  tff(c_2622, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_2614])).
% 7.69/2.62  tff(c_2663, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2622, c_20])).
% 7.69/2.62  tff(c_2667, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2663])).
% 7.69/2.62  tff(c_2593, plain, (![C_415, A_416, B_417]: (r2_hidden(C_415, A_416) | ~r2_hidden(C_415, B_417) | ~m1_subset_1(B_417, k1_zfmisc_1(A_416)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.69/2.62  tff(c_2742, plain, (![A_441, B_442, A_443]: (r2_hidden('#skF_1'(A_441, B_442), A_443) | ~m1_subset_1(A_441, k1_zfmisc_1(A_443)) | r1_tarski(A_441, B_442))), inference(resolution, [status(thm)], [c_6, c_2593])).
% 7.69/2.62  tff(c_2754, plain, (![A_444, A_445]: (~m1_subset_1(A_444, k1_zfmisc_1(A_445)) | r1_tarski(A_444, A_445))), inference(resolution, [status(thm)], [c_2742, c_4])).
% 7.69/2.62  tff(c_2770, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_2667, c_2754])).
% 7.69/2.62  tff(c_2621, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_2614])).
% 7.69/2.62  tff(c_2816, plain, (![B_448, A_449, C_450]: (k1_xboole_0=B_448 | k1_relset_1(A_449, B_448, C_450)=A_449 | ~v1_funct_2(C_450, A_449, B_448) | ~m1_subset_1(C_450, k1_zfmisc_1(k2_zfmisc_1(A_449, B_448))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.69/2.62  tff(c_2823, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_2816])).
% 7.69/2.62  tff(c_2830, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2621, c_2823])).
% 7.69/2.62  tff(c_2831, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_68, c_2830])).
% 7.69/2.62  tff(c_2650, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2621, c_20])).
% 7.69/2.62  tff(c_2654, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2650])).
% 7.69/2.62  tff(c_2771, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_2654, c_2754])).
% 7.69/2.62  tff(c_2793, plain, (k1_relat_1('#skF_6')='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_2771, c_8])).
% 7.69/2.62  tff(c_2812, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_2793])).
% 7.69/2.62  tff(c_2835, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2831, c_2812])).
% 7.69/2.62  tff(c_2841, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2835])).
% 7.69/2.62  tff(c_2842, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitRight, [status(thm)], [c_2793])).
% 7.69/2.62  tff(c_2577, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_2569])).
% 7.69/2.62  tff(c_2534, plain, (r2_hidden('#skF_7', k1_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_56])).
% 7.69/2.62  tff(c_2659, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2622, c_2534])).
% 7.69/2.62  tff(c_3135, plain, (![B_488, C_489, A_490]: (k1_funct_1(B_488, C_489)=k1_funct_1(A_490, C_489) | ~r2_hidden(C_489, k1_relat_1(A_490)) | ~r1_partfun1(A_490, B_488) | ~r1_tarski(k1_relat_1(A_490), k1_relat_1(B_488)) | ~v1_funct_1(B_488) | ~v1_relat_1(B_488) | ~v1_funct_1(A_490) | ~v1_relat_1(A_490))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.69/2.62  tff(c_3150, plain, (![B_488]: (k1_funct_1(B_488, '#skF_7')=k1_funct_1('#skF_5', '#skF_7') | ~r1_partfun1('#skF_5', B_488) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_488)) | ~v1_funct_1(B_488) | ~v1_relat_1(B_488) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_2659, c_3135])).
% 7.69/2.62  tff(c_3867, plain, (![B_605]: (k1_funct_1(B_605, '#skF_7')=k1_funct_1('#skF_5', '#skF_7') | ~r1_partfun1('#skF_5', B_605) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_605)) | ~v1_funct_1(B_605) | ~v1_relat_1(B_605))), inference(demodulation, [status(thm), theory('equality')], [c_2577, c_52, c_3150])).
% 7.69/2.62  tff(c_3870, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_6', '#skF_7') | ~r1_partfun1('#skF_5', '#skF_6') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2842, c_3867])).
% 7.69/2.62  tff(c_3876, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2576, c_48, c_2770, c_2535, c_3870])).
% 7.69/2.62  tff(c_3878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2537, c_3876])).
% 7.69/2.62  tff(c_3880, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_42])).
% 7.69/2.62  tff(c_3879, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_42])).
% 7.69/2.62  tff(c_3886, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3880, c_3879])).
% 7.69/2.62  tff(c_3940, plain, (r2_hidden('#skF_7', k1_relset_1('#skF_4', '#skF_4', '#skF_5')) | ~r1_partfun1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3886, c_56])).
% 7.69/2.62  tff(c_3941, plain, (~r1_partfun1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_3940])).
% 7.69/2.62  tff(c_3898, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_3886, c_44])).
% 7.69/2.62  tff(c_3931, plain, (![C_614, A_615, B_616]: (v1_relat_1(C_614) | ~m1_subset_1(C_614, k1_zfmisc_1(k2_zfmisc_1(A_615, B_616))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.69/2.62  tff(c_3939, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_3898, c_3931])).
% 7.69/2.62  tff(c_3899, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_3886, c_50])).
% 7.69/2.62  tff(c_3938, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3899, c_3931])).
% 7.69/2.62  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.69/2.62  tff(c_3881, plain, (![A_8]: (r1_tarski('#skF_3', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_3879, c_14])).
% 7.69/2.62  tff(c_3896, plain, (![A_8]: (r1_tarski('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_3886, c_3881])).
% 7.69/2.62  tff(c_3962, plain, (![A_626, B_627, C_628]: (k1_relset_1(A_626, B_627, C_628)=k1_relat_1(C_628) | ~m1_subset_1(C_628, k1_zfmisc_1(k2_zfmisc_1(A_626, B_627))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.69/2.62  tff(c_3969, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3899, c_3962])).
% 7.69/2.62  tff(c_4028, plain, (![A_636, B_637, C_638]: (m1_subset_1(k1_relset_1(A_636, B_637, C_638), k1_zfmisc_1(A_636)) | ~m1_subset_1(C_638, k1_zfmisc_1(k2_zfmisc_1(A_636, B_637))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.69/2.62  tff(c_4045, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_3969, c_4028])).
% 7.69/2.62  tff(c_4052, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3899, c_4045])).
% 7.69/2.62  tff(c_3946, plain, (![C_620, A_621, B_622]: (r2_hidden(C_620, A_621) | ~r2_hidden(C_620, B_622) | ~m1_subset_1(B_622, k1_zfmisc_1(A_621)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.69/2.62  tff(c_3981, plain, (![A_630, B_631, A_632]: (r2_hidden('#skF_1'(A_630, B_631), A_632) | ~m1_subset_1(A_630, k1_zfmisc_1(A_632)) | r1_tarski(A_630, B_631))), inference(resolution, [status(thm)], [c_6, c_3946])).
% 7.69/2.62  tff(c_3992, plain, (![A_630, A_632]: (~m1_subset_1(A_630, k1_zfmisc_1(A_632)) | r1_tarski(A_630, A_632))), inference(resolution, [status(thm)], [c_3981, c_4])).
% 7.69/2.62  tff(c_4084, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_4052, c_3992])).
% 7.69/2.62  tff(c_3908, plain, (![B_611, A_612]: (B_611=A_612 | ~r1_tarski(B_611, A_612) | ~r1_tarski(A_612, B_611))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.69/2.62  tff(c_3913, plain, (![A_8]: (A_8='#skF_4' | ~r1_tarski(A_8, '#skF_4'))), inference(resolution, [status(thm)], [c_3896, c_3908])).
% 7.69/2.62  tff(c_4090, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_4084, c_3913])).
% 7.69/2.62  tff(c_4751, plain, (![A_724, B_725]: (r2_hidden('#skF_2'(A_724, B_725), k1_relat_1(A_724)) | r1_partfun1(A_724, B_725) | ~r1_tarski(k1_relat_1(A_724), k1_relat_1(B_725)) | ~v1_funct_1(B_725) | ~v1_relat_1(B_725) | ~v1_funct_1(A_724) | ~v1_relat_1(A_724))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.69/2.62  tff(c_4758, plain, (![B_725]: (r2_hidden('#skF_2'('#skF_5', B_725), '#skF_4') | r1_partfun1('#skF_5', B_725) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_725)) | ~v1_funct_1(B_725) | ~v1_relat_1(B_725) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4090, c_4751])).
% 7.69/2.62  tff(c_4768, plain, (![B_726]: (r2_hidden('#skF_2'('#skF_5', B_726), '#skF_4') | r1_partfun1('#skF_5', B_726) | ~v1_funct_1(B_726) | ~v1_relat_1(B_726))), inference(demodulation, [status(thm), theory('equality')], [c_3938, c_52, c_3896, c_4090, c_4758])).
% 7.69/2.62  tff(c_4002, plain, (![E_42]: (r1_partfun1('#skF_5', '#skF_6') | k1_funct_1('#skF_5', E_42)=k1_funct_1('#skF_6', E_42) | ~r2_hidden(E_42, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_3969, c_3886, c_64])).
% 7.69/2.62  tff(c_4003, plain, (![E_42]: (k1_funct_1('#skF_5', E_42)=k1_funct_1('#skF_6', E_42) | ~r2_hidden(E_42, k1_relat_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_3941, c_4002])).
% 7.69/2.62  tff(c_4096, plain, (![E_42]: (k1_funct_1('#skF_5', E_42)=k1_funct_1('#skF_6', E_42) | ~r2_hidden(E_42, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4090, c_4003])).
% 7.69/2.62  tff(c_5145, plain, (![B_774]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_774))=k1_funct_1('#skF_6', '#skF_2'('#skF_5', B_774)) | r1_partfun1('#skF_5', B_774) | ~v1_funct_1(B_774) | ~v1_relat_1(B_774))), inference(resolution, [status(thm)], [c_4768, c_4096])).
% 7.69/2.62  tff(c_5150, plain, (![B_774]: (k1_funct_1(B_774, '#skF_2'('#skF_5', B_774))!=k1_funct_1('#skF_6', '#skF_2'('#skF_5', B_774)) | r1_partfun1('#skF_5', B_774) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_774)) | ~v1_funct_1(B_774) | ~v1_relat_1(B_774) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | r1_partfun1('#skF_5', B_774) | ~v1_funct_1(B_774) | ~v1_relat_1(B_774))), inference(superposition, [status(thm), theory('equality')], [c_5145, c_38])).
% 7.69/2.62  tff(c_5156, plain, (![B_774]: (k1_funct_1(B_774, '#skF_2'('#skF_5', B_774))!=k1_funct_1('#skF_6', '#skF_2'('#skF_5', B_774)) | r1_partfun1('#skF_5', B_774) | ~v1_funct_1(B_774) | ~v1_relat_1(B_774))), inference(demodulation, [status(thm), theory('equality')], [c_3938, c_52, c_3896, c_4090, c_5150])).
% 7.69/2.62  tff(c_5166, plain, (r1_partfun1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(reflexivity, [status(thm), theory('equality')], [c_5156])).
% 7.69/2.62  tff(c_5168, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3939, c_48, c_5166])).
% 7.69/2.62  tff(c_5170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3941, c_5168])).
% 7.69/2.62  tff(c_5172, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_3940])).
% 7.69/2.62  tff(c_5174, plain, (k1_funct_1('#skF_5', '#skF_7')!=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_5172, c_54])).
% 7.69/2.62  tff(c_5210, plain, (![A_786, B_787, C_788]: (k1_relset_1(A_786, B_787, C_788)=k1_relat_1(C_788) | ~m1_subset_1(C_788, k1_zfmisc_1(k2_zfmisc_1(A_786, B_787))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.69/2.62  tff(c_5217, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3899, c_5210])).
% 7.69/2.62  tff(c_5247, plain, (![A_792, B_793, C_794]: (m1_subset_1(k1_relset_1(A_792, B_793, C_794), k1_zfmisc_1(A_792)) | ~m1_subset_1(C_794, k1_zfmisc_1(k2_zfmisc_1(A_792, B_793))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.69/2.62  tff(c_5261, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5217, c_5247])).
% 7.69/2.62  tff(c_5267, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3899, c_5261])).
% 7.69/2.62  tff(c_5171, plain, (r2_hidden('#skF_7', k1_relset_1('#skF_4', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_3940])).
% 7.69/2.62  tff(c_5190, plain, (![C_779, A_780, B_781]: (r2_hidden(C_779, A_780) | ~r2_hidden(C_779, B_781) | ~m1_subset_1(B_781, k1_zfmisc_1(A_780)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.69/2.62  tff(c_5195, plain, (![A_780]: (r2_hidden('#skF_7', A_780) | ~m1_subset_1(k1_relset_1('#skF_4', '#skF_4', '#skF_5'), k1_zfmisc_1(A_780)))), inference(resolution, [status(thm)], [c_5171, c_5190])).
% 7.69/2.62  tff(c_5219, plain, (![A_780]: (r2_hidden('#skF_7', A_780) | ~m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1(A_780)))), inference(demodulation, [status(thm), theory('equality')], [c_5217, c_5195])).
% 7.69/2.62  tff(c_5271, plain, (r2_hidden('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_5267, c_5219])).
% 7.69/2.62  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.69/2.62  tff(c_5275, plain, (![B_2]: (r2_hidden('#skF_7', B_2) | ~r1_tarski('#skF_4', B_2))), inference(resolution, [status(thm)], [c_5271, c_2])).
% 7.69/2.62  tff(c_5279, plain, (![B_2]: (r2_hidden('#skF_7', B_2))), inference(demodulation, [status(thm), theory('equality')], [c_3896, c_5275])).
% 7.69/2.62  tff(c_5295, plain, (![A_796, B_797, A_798]: (r2_hidden('#skF_1'(A_796, B_797), A_798) | ~m1_subset_1(A_796, k1_zfmisc_1(A_798)) | r1_tarski(A_796, B_797))), inference(resolution, [status(thm)], [c_6, c_5190])).
% 7.69/2.62  tff(c_5307, plain, (![A_799, A_800]: (~m1_subset_1(A_799, k1_zfmisc_1(A_800)) | r1_tarski(A_799, A_800))), inference(resolution, [status(thm)], [c_5295, c_4])).
% 7.69/2.62  tff(c_5323, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_5267, c_5307])).
% 7.69/2.62  tff(c_5333, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_5323, c_3913])).
% 7.69/2.62  tff(c_6115, plain, (![B_914, C_915, A_916]: (k1_funct_1(B_914, C_915)=k1_funct_1(A_916, C_915) | ~r2_hidden(C_915, k1_relat_1(A_916)) | ~r1_partfun1(A_916, B_914) | ~r1_tarski(k1_relat_1(A_916), k1_relat_1(B_914)) | ~v1_funct_1(B_914) | ~v1_relat_1(B_914) | ~v1_funct_1(A_916) | ~v1_relat_1(A_916))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.69/2.62  tff(c_6139, plain, (![B_914, C_915]: (k1_funct_1(B_914, C_915)=k1_funct_1('#skF_5', C_915) | ~r2_hidden(C_915, '#skF_4') | ~r1_partfun1('#skF_5', B_914) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_914)) | ~v1_funct_1(B_914) | ~v1_relat_1(B_914) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5333, c_6115])).
% 7.69/2.62  tff(c_6218, plain, (![B_920, C_921]: (k1_funct_1(B_920, C_921)=k1_funct_1('#skF_5', C_921) | ~r2_hidden(C_921, '#skF_4') | ~r1_partfun1('#skF_5', B_920) | ~v1_funct_1(B_920) | ~v1_relat_1(B_920))), inference(demodulation, [status(thm), theory('equality')], [c_3938, c_52, c_3896, c_5333, c_6139])).
% 7.69/2.62  tff(c_6261, plain, (![B_922]: (k1_funct_1(B_922, '#skF_7')=k1_funct_1('#skF_5', '#skF_7') | ~r1_partfun1('#skF_5', B_922) | ~v1_funct_1(B_922) | ~v1_relat_1(B_922))), inference(resolution, [status(thm)], [c_5279, c_6218])).
% 7.69/2.62  tff(c_6268, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_6', '#skF_7') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_5172, c_6261])).
% 7.69/2.62  tff(c_6275, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3939, c_48, c_6268])).
% 7.69/2.62  tff(c_6277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5174, c_6275])).
% 7.69/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.69/2.62  
% 7.69/2.62  Inference rules
% 7.69/2.62  ----------------------
% 7.69/2.62  #Ref     : 5
% 7.69/2.62  #Sup     : 1453
% 7.69/2.62  #Fact    : 0
% 7.69/2.62  #Define  : 0
% 7.69/2.62  #Split   : 66
% 7.69/2.62  #Chain   : 0
% 7.69/2.62  #Close   : 0
% 7.69/2.62  
% 7.69/2.62  Ordering : KBO
% 7.69/2.62  
% 7.69/2.62  Simplification rules
% 7.69/2.62  ----------------------
% 7.69/2.62  #Subsume      : 565
% 7.69/2.62  #Demod        : 513
% 7.69/2.62  #Tautology    : 249
% 7.69/2.62  #SimpNegUnit  : 21
% 7.69/2.62  #BackRed      : 38
% 7.69/2.62  
% 7.69/2.62  #Partial instantiations: 0
% 7.69/2.62  #Strategies tried      : 1
% 7.69/2.62  
% 7.69/2.62  Timing (in seconds)
% 7.69/2.62  ----------------------
% 7.69/2.62  Preprocessing        : 0.36
% 7.69/2.62  Parsing              : 0.18
% 7.69/2.62  CNF conversion       : 0.03
% 7.69/2.62  Main loop            : 1.47
% 7.69/2.62  Inferencing          : 0.48
% 7.69/2.62  Reduction            : 0.43
% 7.69/2.62  Demodulation         : 0.29
% 7.69/2.62  BG Simplification    : 0.05
% 7.69/2.62  Subsumption          : 0.40
% 7.69/2.62  Abstraction          : 0.06
% 7.69/2.63  MUC search           : 0.00
% 7.69/2.63  Cooper               : 0.00
% 7.69/2.63  Total                : 1.89
% 7.69/2.63  Index Insertion      : 0.00
% 7.69/2.63  Index Deletion       : 0.00
% 7.69/2.63  Index Matching       : 0.00
% 7.69/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
