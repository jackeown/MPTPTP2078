%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:09 EST 2020

% Result     : Theorem 7.53s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :  168 (2185 expanded)
%              Number of leaves         :   37 ( 773 expanded)
%              Depth                    :   27
%              Number of atoms          :  346 (7544 expanded)
%              Number of equality atoms :   64 (1514 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,C)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
               => ( ! [E] :
                      ( m1_subset_1(E,B)
                     => r2_hidden(k3_funct_2(B,C,D,E),A) )
                 => r1_tarski(k2_relset_1(B,C,D),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
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

tff(f_110,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_150,plain,(
    ! [A_64,B_65,C_66] :
      ( k2_relset_1(A_64,B_65,C_66) = k2_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_159,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_150])).

tff(c_52,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_160,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_52])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_18,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_106,plain,(
    ! [B_58,A_59] :
      ( v1_relat_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_112,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_106])).

tff(c_116,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_112])).

tff(c_206,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_215,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_206])).

tff(c_2740,plain,(
    ! [B_297,A_298,C_299] :
      ( k1_xboole_0 = B_297
      | k1_relset_1(A_298,B_297,C_299) = A_298
      | ~ v1_funct_2(C_299,A_298,B_297)
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(A_298,B_297))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2755,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_2740])).

tff(c_2762,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_215,c_2755])).

tff(c_2763,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2762])).

tff(c_46,plain,(
    ! [C_31,B_30] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_31),B_30,C_31),k1_relat_1(C_31))
      | v1_funct_2(C_31,k1_relat_1(C_31),B_30)
      | ~ v1_funct_1(C_31)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2768,plain,(
    ! [B_30] :
      ( r2_hidden('#skF_1'('#skF_3',B_30,'#skF_5'),k1_relat_1('#skF_5'))
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_30)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2763,c_46])).

tff(c_2783,plain,(
    ! [B_300] :
      ( r2_hidden('#skF_1'('#skF_3',B_300,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_300) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_60,c_2763,c_2763,c_2768])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2787,plain,(
    ! [B_300] :
      ( m1_subset_1('#skF_1'('#skF_3',B_300,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_300) ) ),
    inference(resolution,[status(thm)],[c_2783,c_10])).

tff(c_3180,plain,(
    ! [A_344,B_345,C_346,D_347] :
      ( k3_funct_2(A_344,B_345,C_346,D_347) = k1_funct_1(C_346,D_347)
      | ~ m1_subset_1(D_347,A_344)
      | ~ m1_subset_1(C_346,k1_zfmisc_1(k2_zfmisc_1(A_344,B_345)))
      | ~ v1_funct_2(C_346,A_344,B_345)
      | ~ v1_funct_1(C_346)
      | v1_xboole_0(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3188,plain,(
    ! [B_345,C_346,B_300] :
      ( k3_funct_2('#skF_3',B_345,C_346,'#skF_1'('#skF_3',B_300,'#skF_5')) = k1_funct_1(C_346,'#skF_1'('#skF_3',B_300,'#skF_5'))
      | ~ m1_subset_1(C_346,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_345)))
      | ~ v1_funct_2(C_346,'#skF_3',B_345)
      | ~ v1_funct_1(C_346)
      | v1_xboole_0('#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_300) ) ),
    inference(resolution,[status(thm)],[c_2787,c_3180])).

tff(c_3413,plain,(
    ! [B_366,C_367,B_368] :
      ( k3_funct_2('#skF_3',B_366,C_367,'#skF_1'('#skF_3',B_368,'#skF_5')) = k1_funct_1(C_367,'#skF_1'('#skF_3',B_368,'#skF_5'))
      | ~ m1_subset_1(C_367,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_366)))
      | ~ v1_funct_2(C_367,'#skF_3',B_366)
      | ~ v1_funct_1(C_367)
      | v1_funct_2('#skF_5','#skF_3',B_368) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3188])).

tff(c_3426,plain,(
    ! [B_368] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_368,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_368,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_funct_2('#skF_5','#skF_3',B_368) ) ),
    inference(resolution,[status(thm)],[c_56,c_3413])).

tff(c_4326,plain,(
    ! [B_444] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_444,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_444,'#skF_5'))
      | v1_funct_2('#skF_5','#skF_3',B_444) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3426])).

tff(c_54,plain,(
    ! [E_44] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_5',E_44),'#skF_2')
      | ~ m1_subset_1(E_44,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4437,plain,(
    ! [B_456] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_456,'#skF_5')),'#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_456,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_456) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4326,c_54])).

tff(c_2833,plain,(
    ! [C_309,B_310] :
      ( ~ r2_hidden(k1_funct_1(C_309,'#skF_1'(k1_relat_1(C_309),B_310,C_309)),B_310)
      | v1_funct_2(C_309,k1_relat_1(C_309),B_310)
      | ~ v1_funct_1(C_309)
      | ~ v1_relat_1(C_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2836,plain,(
    ! [B_310] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_310,'#skF_5')),B_310)
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_310)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2763,c_2833])).

tff(c_2838,plain,(
    ! [B_310] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_310,'#skF_5')),B_310)
      | v1_funct_2('#skF_5','#skF_3',B_310) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_60,c_2763,c_2836])).

tff(c_4450,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_4437,c_2838])).

tff(c_4452,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4450])).

tff(c_2921,plain,(
    ! [C_319,B_320] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_319),B_320,C_319),k1_relat_1(C_319))
      | m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_319),B_320)))
      | ~ v1_funct_1(C_319)
      | ~ v1_relat_1(C_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2930,plain,(
    ! [B_320] :
      ( r2_hidden('#skF_1'(k1_relat_1('#skF_5'),B_320,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_320)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2763,c_2921])).

tff(c_2975,plain,(
    ! [B_326] :
      ( r2_hidden('#skF_1'('#skF_3',B_326,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_326))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_60,c_2763,c_2763,c_2930])).

tff(c_24,plain,(
    ! [A_19,B_20,C_21] :
      ( k2_relset_1(A_19,B_20,C_21) = k2_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3175,plain,(
    ! [B_343] :
      ( k2_relset_1('#skF_3',B_343,'#skF_5') = k2_relat_1('#skF_5')
      | r2_hidden('#skF_1'('#skF_3',B_343,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2975,c_24])).

tff(c_3179,plain,(
    ! [B_343] :
      ( m1_subset_1('#skF_1'('#skF_3',B_343,'#skF_5'),'#skF_3')
      | k2_relset_1('#skF_3',B_343,'#skF_5') = k2_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3175,c_10])).

tff(c_4466,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3179,c_4452])).

tff(c_216,plain,(
    ! [A_80,B_81,C_82] :
      ( m1_subset_1(k2_relset_1(A_80,B_81,C_82),k1_zfmisc_1(B_81))
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_243,plain,(
    ! [A_80,B_81,C_82] :
      ( r1_tarski(k2_relset_1(A_80,B_81,C_82),B_81)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(resolution,[status(thm)],[c_216,c_12])).

tff(c_3140,plain,(
    ! [B_342] :
      ( r1_tarski(k2_relset_1('#skF_3',B_342,'#skF_5'),B_342)
      | r2_hidden('#skF_1'('#skF_3',B_342,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2975,c_243])).

tff(c_3174,plain,(
    ! [B_342] :
      ( m1_subset_1('#skF_1'('#skF_3',B_342,'#skF_5'),'#skF_3')
      | r1_tarski(k2_relset_1('#skF_3',B_342,'#skF_5'),B_342) ) ),
    inference(resolution,[status(thm)],[c_3140,c_10])).

tff(c_4483,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4466,c_3174])).

tff(c_4498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_4452,c_4483])).

tff(c_4500,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_4450])).

tff(c_38,plain,(
    ! [A_25,B_26,C_27,D_28] :
      ( k3_funct_2(A_25,B_26,C_27,D_28) = k1_funct_1(C_27,D_28)
      | ~ m1_subset_1(D_28,A_25)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_2(C_27,A_25,B_26)
      | ~ v1_funct_1(C_27)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4517,plain,(
    ! [B_26,C_27] :
      ( k3_funct_2('#skF_3',B_26,C_27,'#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1(C_27,'#skF_1'('#skF_3','#skF_2','#skF_5'))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_26)))
      | ~ v1_funct_2(C_27,'#skF_3',B_26)
      | ~ v1_funct_1(C_27)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4500,c_38])).

tff(c_4523,plain,(
    ! [B_460,C_461] :
      ( k3_funct_2('#skF_3',B_460,C_461,'#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1(C_461,'#skF_1'('#skF_3','#skF_2','#skF_5'))
      | ~ m1_subset_1(C_461,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_460)))
      | ~ v1_funct_2(C_461,'#skF_3',B_460)
      | ~ v1_funct_1(C_461) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4517])).

tff(c_4552,plain,
    ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5'))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_4523])).

tff(c_4566,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_4552])).

tff(c_4576,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4566,c_54])).

tff(c_4587,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4500,c_4576])).

tff(c_3074,plain,(
    ! [C_334,B_335] :
      ( ~ r2_hidden(k1_funct_1(C_334,'#skF_1'(k1_relat_1(C_334),B_335,C_334)),B_335)
      | m1_subset_1(C_334,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_334),B_335)))
      | ~ v1_funct_1(C_334)
      | ~ v1_relat_1(C_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_3077,plain,(
    ! [B_335] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_335,'#skF_5')),B_335)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_335)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2763,c_3074])).

tff(c_3079,plain,(
    ! [B_335] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_335,'#skF_5')),B_335)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_335))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_60,c_2763,c_3077])).

tff(c_4603,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_4587,c_3079])).

tff(c_4679,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4603,c_12])).

tff(c_4675,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4603,c_24])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2842,plain,(
    ! [A_311,B_312,C_313] :
      ( r1_tarski(k2_relset_1(A_311,B_312,C_313),B_312)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(k2_zfmisc_1(A_311,B_312))) ) ),
    inference(resolution,[status(thm)],[c_216,c_12])).

tff(c_2857,plain,(
    ! [A_311,B_312,A_6] :
      ( r1_tarski(k2_relset_1(A_311,B_312,A_6),B_312)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_311,B_312)) ) ),
    inference(resolution,[status(thm)],[c_14,c_2842])).

tff(c_4764,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_2')
    | ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4675,c_2857])).

tff(c_4777,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4679,c_4764])).

tff(c_4779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_4777])).

tff(c_4780,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2762])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4795,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4780,c_8])).

tff(c_239,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_216])).

tff(c_245,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_239])).

tff(c_253,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_245,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_260,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_253,c_2])).

tff(c_2535,plain,(
    ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_4803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4795,c_2535])).

tff(c_4804,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_4809,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4804,c_160])).

tff(c_5041,plain,(
    ! [B_488,A_489,C_490] :
      ( k1_xboole_0 = B_488
      | k1_relset_1(A_489,B_488,C_490) = A_489
      | ~ v1_funct_2(C_490,A_489,B_488)
      | ~ m1_subset_1(C_490,k1_zfmisc_1(k2_zfmisc_1(A_489,B_488))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5056,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_5041])).

tff(c_5063,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_215,c_5056])).

tff(c_5064,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5063])).

tff(c_5069,plain,(
    ! [B_30] :
      ( r2_hidden('#skF_1'('#skF_3',B_30,'#skF_5'),k1_relat_1('#skF_5'))
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_30)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5064,c_46])).

tff(c_5084,plain,(
    ! [B_491] :
      ( r2_hidden('#skF_1'('#skF_3',B_491,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_491) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_60,c_5064,c_5064,c_5069])).

tff(c_5088,plain,(
    ! [B_491] :
      ( m1_subset_1('#skF_1'('#skF_3',B_491,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_491) ) ),
    inference(resolution,[status(thm)],[c_5084,c_10])).

tff(c_5601,plain,(
    ! [A_548,B_549,C_550,D_551] :
      ( k3_funct_2(A_548,B_549,C_550,D_551) = k1_funct_1(C_550,D_551)
      | ~ m1_subset_1(D_551,A_548)
      | ~ m1_subset_1(C_550,k1_zfmisc_1(k2_zfmisc_1(A_548,B_549)))
      | ~ v1_funct_2(C_550,A_548,B_549)
      | ~ v1_funct_1(C_550)
      | v1_xboole_0(A_548) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5611,plain,(
    ! [B_549,C_550,B_491] :
      ( k3_funct_2('#skF_3',B_549,C_550,'#skF_1'('#skF_3',B_491,'#skF_5')) = k1_funct_1(C_550,'#skF_1'('#skF_3',B_491,'#skF_5'))
      | ~ m1_subset_1(C_550,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_549)))
      | ~ v1_funct_2(C_550,'#skF_3',B_549)
      | ~ v1_funct_1(C_550)
      | v1_xboole_0('#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_491) ) ),
    inference(resolution,[status(thm)],[c_5088,c_5601])).

tff(c_5806,plain,(
    ! [B_566,C_567,B_568] :
      ( k3_funct_2('#skF_3',B_566,C_567,'#skF_1'('#skF_3',B_568,'#skF_5')) = k1_funct_1(C_567,'#skF_1'('#skF_3',B_568,'#skF_5'))
      | ~ m1_subset_1(C_567,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_566)))
      | ~ v1_funct_2(C_567,'#skF_3',B_566)
      | ~ v1_funct_1(C_567)
      | v1_funct_2('#skF_5','#skF_3',B_568) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5611])).

tff(c_5819,plain,(
    ! [B_568] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_568,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_568,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_funct_2('#skF_5','#skF_3',B_568) ) ),
    inference(resolution,[status(thm)],[c_56,c_5806])).

tff(c_6719,plain,(
    ! [B_646] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_646,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_646,'#skF_5'))
      | v1_funct_2('#skF_5','#skF_3',B_646) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_5819])).

tff(c_6782,plain,(
    ! [B_649] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_649,'#skF_5')),'#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_649,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_649) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6719,c_54])).

tff(c_5217,plain,(
    ! [C_508,B_509] :
      ( ~ r2_hidden(k1_funct_1(C_508,'#skF_1'(k1_relat_1(C_508),B_509,C_508)),B_509)
      | v1_funct_2(C_508,k1_relat_1(C_508),B_509)
      | ~ v1_funct_1(C_508)
      | ~ v1_relat_1(C_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_5220,plain,(
    ! [B_509] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_509,'#skF_5')),B_509)
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_509)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5064,c_5217])).

tff(c_5222,plain,(
    ! [B_509] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_509,'#skF_5')),B_509)
      | v1_funct_2('#skF_5','#skF_3',B_509) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_60,c_5064,c_5220])).

tff(c_6795,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_6782,c_5222])).

tff(c_6812,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6795])).

tff(c_5351,plain,(
    ! [C_527,B_528] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_527),B_528,C_527),k1_relat_1(C_527))
      | m1_subset_1(C_527,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_527),B_528)))
      | ~ v1_funct_1(C_527)
      | ~ v1_relat_1(C_527) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_5357,plain,(
    ! [B_528] :
      ( r2_hidden('#skF_1'('#skF_3',B_528,'#skF_5'),k1_relat_1('#skF_5'))
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_528)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5064,c_5351])).

tff(c_5366,plain,(
    ! [B_529] :
      ( r2_hidden('#skF_1'('#skF_3',B_529,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_529))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_60,c_5064,c_5064,c_5357])).

tff(c_5384,plain,(
    ! [B_529] :
      ( k2_relset_1('#skF_3',B_529,'#skF_5') = k2_relat_1('#skF_5')
      | r2_hidden('#skF_1'('#skF_3',B_529,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5366,c_24])).

tff(c_5413,plain,(
    ! [B_532] :
      ( k2_relset_1('#skF_3',B_532,'#skF_5') = '#skF_4'
      | r2_hidden('#skF_1'('#skF_3',B_532,'#skF_5'),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4804,c_5384])).

tff(c_5417,plain,(
    ! [B_532] :
      ( m1_subset_1('#skF_1'('#skF_3',B_532,'#skF_5'),'#skF_3')
      | k2_relset_1('#skF_3',B_532,'#skF_5') = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_5413,c_10])).

tff(c_6826,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5417,c_6812])).

tff(c_5456,plain,(
    ! [B_538] :
      ( r1_tarski(k2_relset_1('#skF_3',B_538,'#skF_5'),B_538)
      | r2_hidden('#skF_1'('#skF_3',B_538,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5366,c_243])).

tff(c_5490,plain,(
    ! [B_538] :
      ( m1_subset_1('#skF_1'('#skF_3',B_538,'#skF_5'),'#skF_3')
      | r1_tarski(k2_relset_1('#skF_3',B_538,'#skF_5'),B_538) ) ),
    inference(resolution,[status(thm)],[c_5456,c_10])).

tff(c_6875,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | r1_tarski('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6826,c_5490])).

tff(c_6890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4809,c_6812,c_6875])).

tff(c_6892,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_6795])).

tff(c_6894,plain,(
    ! [B_26,C_27] :
      ( k3_funct_2('#skF_3',B_26,C_27,'#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1(C_27,'#skF_1'('#skF_3','#skF_2','#skF_5'))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_26)))
      | ~ v1_funct_2(C_27,'#skF_3',B_26)
      | ~ v1_funct_1(C_27)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6892,c_38])).

tff(c_7071,plain,(
    ! [B_672,C_673] :
      ( k3_funct_2('#skF_3',B_672,C_673,'#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1(C_673,'#skF_1'('#skF_3','#skF_2','#skF_5'))
      | ~ m1_subset_1(C_673,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_672)))
      | ~ v1_funct_2(C_673,'#skF_3',B_672)
      | ~ v1_funct_1(C_673) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_6894])).

tff(c_7100,plain,
    ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5'))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_7071])).

tff(c_7114,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_7100])).

tff(c_7124,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7114,c_54])).

tff(c_7135,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6892,c_7124])).

tff(c_5450,plain,(
    ! [C_536,B_537] :
      ( ~ r2_hidden(k1_funct_1(C_536,'#skF_1'(k1_relat_1(C_536),B_537,C_536)),B_537)
      | m1_subset_1(C_536,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_536),B_537)))
      | ~ v1_funct_1(C_536)
      | ~ v1_relat_1(C_536) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_5453,plain,(
    ! [B_537] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_537,'#skF_5')),B_537)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_537)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5064,c_5450])).

tff(c_5455,plain,(
    ! [B_537] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_537,'#skF_5')),B_537)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_537))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_60,c_5064,c_5453])).

tff(c_7151,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_7135,c_5455])).

tff(c_7188,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_7151,c_24])).

tff(c_7224,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4804,c_7188])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] :
      ( m1_subset_1(k2_relset_1(A_13,B_14,C_15),k1_zfmisc_1(B_14))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_7282,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7224,c_20])).

tff(c_7292,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7151,c_7282])).

tff(c_7301,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_7292,c_12])).

tff(c_7308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4809,c_7301])).

tff(c_7309,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5063])).

tff(c_7323,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7309,c_8])).

tff(c_7331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7323,c_4809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.53/2.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/2.62  
% 7.73/2.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/2.63  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 7.73/2.63  
% 7.73/2.63  %Foreground sorts:
% 7.73/2.63  
% 7.73/2.63  
% 7.73/2.63  %Background operators:
% 7.73/2.63  
% 7.73/2.63  
% 7.73/2.63  %Foreground operators:
% 7.73/2.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.73/2.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.73/2.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.73/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.73/2.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.73/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.73/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.73/2.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.73/2.63  tff('#skF_5', type, '#skF_5': $i).
% 7.73/2.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.73/2.63  tff('#skF_2', type, '#skF_2': $i).
% 7.73/2.63  tff('#skF_3', type, '#skF_3': $i).
% 7.73/2.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.73/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.73/2.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.73/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.73/2.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.73/2.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.73/2.63  tff('#skF_4', type, '#skF_4': $i).
% 7.73/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.73/2.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.73/2.63  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 7.73/2.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.73/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.73/2.63  
% 7.73/2.66  tff(f_132, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 7.73/2.66  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.73/2.66  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.73/2.66  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.73/2.66  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.73/2.66  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.73/2.66  tff(f_110, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 7.73/2.66  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 7.73/2.66  tff(f_93, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 7.73/2.66  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 7.73/2.66  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.73/2.66  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.73/2.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.73/2.66  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.73/2.66  tff(c_150, plain, (![A_64, B_65, C_66]: (k2_relset_1(A_64, B_65, C_66)=k2_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.73/2.66  tff(c_159, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_150])).
% 7.73/2.66  tff(c_52, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.73/2.66  tff(c_160, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_52])).
% 7.73/2.66  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.73/2.66  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.73/2.66  tff(c_64, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.73/2.66  tff(c_18, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.73/2.66  tff(c_106, plain, (![B_58, A_59]: (v1_relat_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.73/2.66  tff(c_112, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_106])).
% 7.73/2.66  tff(c_116, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_112])).
% 7.73/2.66  tff(c_206, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.73/2.66  tff(c_215, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_206])).
% 7.73/2.66  tff(c_2740, plain, (![B_297, A_298, C_299]: (k1_xboole_0=B_297 | k1_relset_1(A_298, B_297, C_299)=A_298 | ~v1_funct_2(C_299, A_298, B_297) | ~m1_subset_1(C_299, k1_zfmisc_1(k2_zfmisc_1(A_298, B_297))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.73/2.66  tff(c_2755, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_2740])).
% 7.73/2.66  tff(c_2762, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_215, c_2755])).
% 7.73/2.66  tff(c_2763, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_2762])).
% 7.73/2.66  tff(c_46, plain, (![C_31, B_30]: (r2_hidden('#skF_1'(k1_relat_1(C_31), B_30, C_31), k1_relat_1(C_31)) | v1_funct_2(C_31, k1_relat_1(C_31), B_30) | ~v1_funct_1(C_31) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.73/2.66  tff(c_2768, plain, (![B_30]: (r2_hidden('#skF_1'('#skF_3', B_30, '#skF_5'), k1_relat_1('#skF_5')) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_30) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2763, c_46])).
% 7.73/2.66  tff(c_2783, plain, (![B_300]: (r2_hidden('#skF_1'('#skF_3', B_300, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_300))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_60, c_2763, c_2763, c_2768])).
% 7.73/2.66  tff(c_10, plain, (![A_4, B_5]: (m1_subset_1(A_4, B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.73/2.66  tff(c_2787, plain, (![B_300]: (m1_subset_1('#skF_1'('#skF_3', B_300, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_300))), inference(resolution, [status(thm)], [c_2783, c_10])).
% 7.73/2.66  tff(c_3180, plain, (![A_344, B_345, C_346, D_347]: (k3_funct_2(A_344, B_345, C_346, D_347)=k1_funct_1(C_346, D_347) | ~m1_subset_1(D_347, A_344) | ~m1_subset_1(C_346, k1_zfmisc_1(k2_zfmisc_1(A_344, B_345))) | ~v1_funct_2(C_346, A_344, B_345) | ~v1_funct_1(C_346) | v1_xboole_0(A_344))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.73/2.66  tff(c_3188, plain, (![B_345, C_346, B_300]: (k3_funct_2('#skF_3', B_345, C_346, '#skF_1'('#skF_3', B_300, '#skF_5'))=k1_funct_1(C_346, '#skF_1'('#skF_3', B_300, '#skF_5')) | ~m1_subset_1(C_346, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_345))) | ~v1_funct_2(C_346, '#skF_3', B_345) | ~v1_funct_1(C_346) | v1_xboole_0('#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_300))), inference(resolution, [status(thm)], [c_2787, c_3180])).
% 7.73/2.66  tff(c_3413, plain, (![B_366, C_367, B_368]: (k3_funct_2('#skF_3', B_366, C_367, '#skF_1'('#skF_3', B_368, '#skF_5'))=k1_funct_1(C_367, '#skF_1'('#skF_3', B_368, '#skF_5')) | ~m1_subset_1(C_367, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_366))) | ~v1_funct_2(C_367, '#skF_3', B_366) | ~v1_funct_1(C_367) | v1_funct_2('#skF_5', '#skF_3', B_368))), inference(negUnitSimplification, [status(thm)], [c_64, c_3188])).
% 7.73/2.66  tff(c_3426, plain, (![B_368]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_368, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_368, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_funct_2('#skF_5', '#skF_3', B_368))), inference(resolution, [status(thm)], [c_56, c_3413])).
% 7.73/2.66  tff(c_4326, plain, (![B_444]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_444, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_444, '#skF_5')) | v1_funct_2('#skF_5', '#skF_3', B_444))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3426])).
% 7.73/2.66  tff(c_54, plain, (![E_44]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_5', E_44), '#skF_2') | ~m1_subset_1(E_44, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.73/2.66  tff(c_4437, plain, (![B_456]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_456, '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', B_456, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_456))), inference(superposition, [status(thm), theory('equality')], [c_4326, c_54])).
% 7.73/2.66  tff(c_2833, plain, (![C_309, B_310]: (~r2_hidden(k1_funct_1(C_309, '#skF_1'(k1_relat_1(C_309), B_310, C_309)), B_310) | v1_funct_2(C_309, k1_relat_1(C_309), B_310) | ~v1_funct_1(C_309) | ~v1_relat_1(C_309))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.73/2.66  tff(c_2836, plain, (![B_310]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_310, '#skF_5')), B_310) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_310) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2763, c_2833])).
% 7.73/2.66  tff(c_2838, plain, (![B_310]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_310, '#skF_5')), B_310) | v1_funct_2('#skF_5', '#skF_3', B_310))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_60, c_2763, c_2836])).
% 7.73/2.66  tff(c_4450, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_4437, c_2838])).
% 7.73/2.66  tff(c_4452, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_4450])).
% 7.73/2.66  tff(c_2921, plain, (![C_319, B_320]: (r2_hidden('#skF_1'(k1_relat_1(C_319), B_320, C_319), k1_relat_1(C_319)) | m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_319), B_320))) | ~v1_funct_1(C_319) | ~v1_relat_1(C_319))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.73/2.66  tff(c_2930, plain, (![B_320]: (r2_hidden('#skF_1'(k1_relat_1('#skF_5'), B_320, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_320))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2763, c_2921])).
% 7.73/2.66  tff(c_2975, plain, (![B_326]: (r2_hidden('#skF_1'('#skF_3', B_326, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_326))))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_60, c_2763, c_2763, c_2930])).
% 7.73/2.66  tff(c_24, plain, (![A_19, B_20, C_21]: (k2_relset_1(A_19, B_20, C_21)=k2_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.73/2.66  tff(c_3175, plain, (![B_343]: (k2_relset_1('#skF_3', B_343, '#skF_5')=k2_relat_1('#skF_5') | r2_hidden('#skF_1'('#skF_3', B_343, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_2975, c_24])).
% 7.73/2.66  tff(c_3179, plain, (![B_343]: (m1_subset_1('#skF_1'('#skF_3', B_343, '#skF_5'), '#skF_3') | k2_relset_1('#skF_3', B_343, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_3175, c_10])).
% 7.73/2.66  tff(c_4466, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3179, c_4452])).
% 7.73/2.66  tff(c_216, plain, (![A_80, B_81, C_82]: (m1_subset_1(k2_relset_1(A_80, B_81, C_82), k1_zfmisc_1(B_81)) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.73/2.66  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.73/2.66  tff(c_243, plain, (![A_80, B_81, C_82]: (r1_tarski(k2_relset_1(A_80, B_81, C_82), B_81) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(resolution, [status(thm)], [c_216, c_12])).
% 7.73/2.66  tff(c_3140, plain, (![B_342]: (r1_tarski(k2_relset_1('#skF_3', B_342, '#skF_5'), B_342) | r2_hidden('#skF_1'('#skF_3', B_342, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_2975, c_243])).
% 7.73/2.66  tff(c_3174, plain, (![B_342]: (m1_subset_1('#skF_1'('#skF_3', B_342, '#skF_5'), '#skF_3') | r1_tarski(k2_relset_1('#skF_3', B_342, '#skF_5'), B_342))), inference(resolution, [status(thm)], [c_3140, c_10])).
% 7.73/2.66  tff(c_4483, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4466, c_3174])).
% 7.73/2.66  tff(c_4498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_4452, c_4483])).
% 7.73/2.66  tff(c_4500, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_4450])).
% 7.73/2.66  tff(c_38, plain, (![A_25, B_26, C_27, D_28]: (k3_funct_2(A_25, B_26, C_27, D_28)=k1_funct_1(C_27, D_28) | ~m1_subset_1(D_28, A_25) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_2(C_27, A_25, B_26) | ~v1_funct_1(C_27) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.73/2.66  tff(c_4517, plain, (![B_26, C_27]: (k3_funct_2('#skF_3', B_26, C_27, '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1(C_27, '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_26))) | ~v1_funct_2(C_27, '#skF_3', B_26) | ~v1_funct_1(C_27) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_4500, c_38])).
% 7.73/2.66  tff(c_4523, plain, (![B_460, C_461]: (k3_funct_2('#skF_3', B_460, C_461, '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1(C_461, '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~m1_subset_1(C_461, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_460))) | ~v1_funct_2(C_461, '#skF_3', B_460) | ~v1_funct_1(C_461))), inference(negUnitSimplification, [status(thm)], [c_64, c_4517])).
% 7.73/2.66  tff(c_4552, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_4523])).
% 7.73/2.66  tff(c_4566, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_4552])).
% 7.73/2.66  tff(c_4576, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4566, c_54])).
% 7.73/2.66  tff(c_4587, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4500, c_4576])).
% 7.73/2.66  tff(c_3074, plain, (![C_334, B_335]: (~r2_hidden(k1_funct_1(C_334, '#skF_1'(k1_relat_1(C_334), B_335, C_334)), B_335) | m1_subset_1(C_334, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_334), B_335))) | ~v1_funct_1(C_334) | ~v1_relat_1(C_334))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.73/2.66  tff(c_3077, plain, (![B_335]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_335, '#skF_5')), B_335) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_335))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2763, c_3074])).
% 7.73/2.66  tff(c_3079, plain, (![B_335]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_335, '#skF_5')), B_335) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_335))))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_60, c_2763, c_3077])).
% 7.73/2.66  tff(c_4603, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_4587, c_3079])).
% 7.73/2.66  tff(c_4679, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_4603, c_12])).
% 7.73/2.66  tff(c_4675, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4603, c_24])).
% 7.73/2.66  tff(c_14, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.73/2.66  tff(c_2842, plain, (![A_311, B_312, C_313]: (r1_tarski(k2_relset_1(A_311, B_312, C_313), B_312) | ~m1_subset_1(C_313, k1_zfmisc_1(k2_zfmisc_1(A_311, B_312))))), inference(resolution, [status(thm)], [c_216, c_12])).
% 7.73/2.66  tff(c_2857, plain, (![A_311, B_312, A_6]: (r1_tarski(k2_relset_1(A_311, B_312, A_6), B_312) | ~r1_tarski(A_6, k2_zfmisc_1(A_311, B_312)))), inference(resolution, [status(thm)], [c_14, c_2842])).
% 7.73/2.66  tff(c_4764, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_2') | ~r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4675, c_2857])).
% 7.73/2.66  tff(c_4777, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4679, c_4764])).
% 7.73/2.66  tff(c_4779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_4777])).
% 7.73/2.66  tff(c_4780, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2762])).
% 7.73/2.66  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.73/2.66  tff(c_4795, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4780, c_8])).
% 7.73/2.66  tff(c_239, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_159, c_216])).
% 7.73/2.66  tff(c_245, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_239])).
% 7.73/2.66  tff(c_253, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_245, c_12])).
% 7.73/2.66  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.73/2.66  tff(c_260, plain, (k2_relat_1('#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_253, c_2])).
% 7.73/2.66  tff(c_2535, plain, (~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_260])).
% 7.73/2.66  tff(c_4803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4795, c_2535])).
% 7.73/2.66  tff(c_4804, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_260])).
% 7.73/2.66  tff(c_4809, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4804, c_160])).
% 7.73/2.66  tff(c_5041, plain, (![B_488, A_489, C_490]: (k1_xboole_0=B_488 | k1_relset_1(A_489, B_488, C_490)=A_489 | ~v1_funct_2(C_490, A_489, B_488) | ~m1_subset_1(C_490, k1_zfmisc_1(k2_zfmisc_1(A_489, B_488))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.73/2.66  tff(c_5056, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_5041])).
% 7.73/2.66  tff(c_5063, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_215, c_5056])).
% 7.73/2.66  tff(c_5064, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_5063])).
% 7.73/2.66  tff(c_5069, plain, (![B_30]: (r2_hidden('#skF_1'('#skF_3', B_30, '#skF_5'), k1_relat_1('#skF_5')) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_30) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5064, c_46])).
% 7.73/2.66  tff(c_5084, plain, (![B_491]: (r2_hidden('#skF_1'('#skF_3', B_491, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_491))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_60, c_5064, c_5064, c_5069])).
% 7.73/2.66  tff(c_5088, plain, (![B_491]: (m1_subset_1('#skF_1'('#skF_3', B_491, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_491))), inference(resolution, [status(thm)], [c_5084, c_10])).
% 7.73/2.66  tff(c_5601, plain, (![A_548, B_549, C_550, D_551]: (k3_funct_2(A_548, B_549, C_550, D_551)=k1_funct_1(C_550, D_551) | ~m1_subset_1(D_551, A_548) | ~m1_subset_1(C_550, k1_zfmisc_1(k2_zfmisc_1(A_548, B_549))) | ~v1_funct_2(C_550, A_548, B_549) | ~v1_funct_1(C_550) | v1_xboole_0(A_548))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.73/2.66  tff(c_5611, plain, (![B_549, C_550, B_491]: (k3_funct_2('#skF_3', B_549, C_550, '#skF_1'('#skF_3', B_491, '#skF_5'))=k1_funct_1(C_550, '#skF_1'('#skF_3', B_491, '#skF_5')) | ~m1_subset_1(C_550, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_549))) | ~v1_funct_2(C_550, '#skF_3', B_549) | ~v1_funct_1(C_550) | v1_xboole_0('#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_491))), inference(resolution, [status(thm)], [c_5088, c_5601])).
% 7.73/2.66  tff(c_5806, plain, (![B_566, C_567, B_568]: (k3_funct_2('#skF_3', B_566, C_567, '#skF_1'('#skF_3', B_568, '#skF_5'))=k1_funct_1(C_567, '#skF_1'('#skF_3', B_568, '#skF_5')) | ~m1_subset_1(C_567, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_566))) | ~v1_funct_2(C_567, '#skF_3', B_566) | ~v1_funct_1(C_567) | v1_funct_2('#skF_5', '#skF_3', B_568))), inference(negUnitSimplification, [status(thm)], [c_64, c_5611])).
% 7.73/2.66  tff(c_5819, plain, (![B_568]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_568, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_568, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_funct_2('#skF_5', '#skF_3', B_568))), inference(resolution, [status(thm)], [c_56, c_5806])).
% 7.73/2.66  tff(c_6719, plain, (![B_646]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_646, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_646, '#skF_5')) | v1_funct_2('#skF_5', '#skF_3', B_646))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_5819])).
% 7.73/2.66  tff(c_6782, plain, (![B_649]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_649, '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', B_649, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_649))), inference(superposition, [status(thm), theory('equality')], [c_6719, c_54])).
% 7.73/2.66  tff(c_5217, plain, (![C_508, B_509]: (~r2_hidden(k1_funct_1(C_508, '#skF_1'(k1_relat_1(C_508), B_509, C_508)), B_509) | v1_funct_2(C_508, k1_relat_1(C_508), B_509) | ~v1_funct_1(C_508) | ~v1_relat_1(C_508))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.73/2.66  tff(c_5220, plain, (![B_509]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_509, '#skF_5')), B_509) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_509) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5064, c_5217])).
% 7.73/2.66  tff(c_5222, plain, (![B_509]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_509, '#skF_5')), B_509) | v1_funct_2('#skF_5', '#skF_3', B_509))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_60, c_5064, c_5220])).
% 7.73/2.66  tff(c_6795, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_6782, c_5222])).
% 7.73/2.66  tff(c_6812, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_6795])).
% 7.73/2.66  tff(c_5351, plain, (![C_527, B_528]: (r2_hidden('#skF_1'(k1_relat_1(C_527), B_528, C_527), k1_relat_1(C_527)) | m1_subset_1(C_527, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_527), B_528))) | ~v1_funct_1(C_527) | ~v1_relat_1(C_527))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.73/2.66  tff(c_5357, plain, (![B_528]: (r2_hidden('#skF_1'('#skF_3', B_528, '#skF_5'), k1_relat_1('#skF_5')) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_528))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5064, c_5351])).
% 7.73/2.66  tff(c_5366, plain, (![B_529]: (r2_hidden('#skF_1'('#skF_3', B_529, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_529))))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_60, c_5064, c_5064, c_5357])).
% 7.73/2.66  tff(c_5384, plain, (![B_529]: (k2_relset_1('#skF_3', B_529, '#skF_5')=k2_relat_1('#skF_5') | r2_hidden('#skF_1'('#skF_3', B_529, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_5366, c_24])).
% 7.73/2.66  tff(c_5413, plain, (![B_532]: (k2_relset_1('#skF_3', B_532, '#skF_5')='#skF_4' | r2_hidden('#skF_1'('#skF_3', B_532, '#skF_5'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4804, c_5384])).
% 7.73/2.66  tff(c_5417, plain, (![B_532]: (m1_subset_1('#skF_1'('#skF_3', B_532, '#skF_5'), '#skF_3') | k2_relset_1('#skF_3', B_532, '#skF_5')='#skF_4')), inference(resolution, [status(thm)], [c_5413, c_10])).
% 7.73/2.66  tff(c_6826, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_5417, c_6812])).
% 7.73/2.66  tff(c_5456, plain, (![B_538]: (r1_tarski(k2_relset_1('#skF_3', B_538, '#skF_5'), B_538) | r2_hidden('#skF_1'('#skF_3', B_538, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_5366, c_243])).
% 7.73/2.66  tff(c_5490, plain, (![B_538]: (m1_subset_1('#skF_1'('#skF_3', B_538, '#skF_5'), '#skF_3') | r1_tarski(k2_relset_1('#skF_3', B_538, '#skF_5'), B_538))), inference(resolution, [status(thm)], [c_5456, c_10])).
% 7.73/2.66  tff(c_6875, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | r1_tarski('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6826, c_5490])).
% 7.73/2.66  tff(c_6890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4809, c_6812, c_6875])).
% 7.73/2.66  tff(c_6892, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_6795])).
% 7.73/2.66  tff(c_6894, plain, (![B_26, C_27]: (k3_funct_2('#skF_3', B_26, C_27, '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1(C_27, '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_26))) | ~v1_funct_2(C_27, '#skF_3', B_26) | ~v1_funct_1(C_27) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_6892, c_38])).
% 7.73/2.66  tff(c_7071, plain, (![B_672, C_673]: (k3_funct_2('#skF_3', B_672, C_673, '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1(C_673, '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~m1_subset_1(C_673, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_672))) | ~v1_funct_2(C_673, '#skF_3', B_672) | ~v1_funct_1(C_673))), inference(negUnitSimplification, [status(thm)], [c_64, c_6894])).
% 7.73/2.66  tff(c_7100, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_7071])).
% 7.73/2.66  tff(c_7114, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_7100])).
% 7.73/2.66  tff(c_7124, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7114, c_54])).
% 7.73/2.66  tff(c_7135, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6892, c_7124])).
% 7.73/2.66  tff(c_5450, plain, (![C_536, B_537]: (~r2_hidden(k1_funct_1(C_536, '#skF_1'(k1_relat_1(C_536), B_537, C_536)), B_537) | m1_subset_1(C_536, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_536), B_537))) | ~v1_funct_1(C_536) | ~v1_relat_1(C_536))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.73/2.66  tff(c_5453, plain, (![B_537]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_537, '#skF_5')), B_537) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_537))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5064, c_5450])).
% 7.73/2.66  tff(c_5455, plain, (![B_537]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_537, '#skF_5')), B_537) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_537))))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_60, c_5064, c_5453])).
% 7.73/2.66  tff(c_7151, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_7135, c_5455])).
% 7.73/2.66  tff(c_7188, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_7151, c_24])).
% 7.73/2.66  tff(c_7224, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4804, c_7188])).
% 7.73/2.66  tff(c_20, plain, (![A_13, B_14, C_15]: (m1_subset_1(k2_relset_1(A_13, B_14, C_15), k1_zfmisc_1(B_14)) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.73/2.66  tff(c_7282, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_7224, c_20])).
% 7.73/2.66  tff(c_7292, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7151, c_7282])).
% 7.73/2.66  tff(c_7301, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_7292, c_12])).
% 7.73/2.66  tff(c_7308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4809, c_7301])).
% 7.73/2.66  tff(c_7309, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_5063])).
% 7.73/2.66  tff(c_7323, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_7309, c_8])).
% 7.73/2.66  tff(c_7331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7323, c_4809])).
% 7.73/2.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/2.66  
% 7.73/2.66  Inference rules
% 7.73/2.66  ----------------------
% 7.73/2.66  #Ref     : 0
% 7.73/2.66  #Sup     : 1503
% 7.73/2.66  #Fact    : 0
% 7.73/2.66  #Define  : 0
% 7.73/2.66  #Split   : 26
% 7.73/2.66  #Chain   : 0
% 7.73/2.66  #Close   : 0
% 7.73/2.66  
% 7.73/2.66  Ordering : KBO
% 7.73/2.66  
% 7.73/2.66  Simplification rules
% 7.73/2.66  ----------------------
% 7.73/2.66  #Subsume      : 160
% 7.73/2.66  #Demod        : 1062
% 7.73/2.66  #Tautology    : 489
% 7.73/2.66  #SimpNegUnit  : 59
% 7.73/2.66  #BackRed      : 69
% 7.73/2.66  
% 7.73/2.66  #Partial instantiations: 0
% 7.73/2.66  #Strategies tried      : 1
% 7.73/2.66  
% 7.73/2.66  Timing (in seconds)
% 7.73/2.66  ----------------------
% 7.73/2.67  Preprocessing        : 0.35
% 7.73/2.67  Parsing              : 0.18
% 7.73/2.67  CNF conversion       : 0.02
% 7.73/2.67  Main loop            : 1.50
% 7.73/2.67  Inferencing          : 0.52
% 7.73/2.67  Reduction            : 0.53
% 7.73/2.67  Demodulation         : 0.37
% 7.73/2.67  BG Simplification    : 0.06
% 7.73/2.67  Subsumption          : 0.25
% 7.73/2.67  Abstraction          : 0.09
% 7.73/2.67  MUC search           : 0.00
% 7.73/2.67  Cooper               : 0.00
% 7.73/2.67  Total                : 1.94
% 7.73/2.67  Index Insertion      : 0.00
% 7.73/2.67  Index Deletion       : 0.00
% 7.73/2.67  Index Matching       : 0.00
% 7.73/2.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
