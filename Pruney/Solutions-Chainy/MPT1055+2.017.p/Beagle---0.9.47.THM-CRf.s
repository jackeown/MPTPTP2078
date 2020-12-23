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
% DateTime   : Thu Dec  3 10:17:21 EST 2020

% Result     : Theorem 6.22s
% Output     : CNFRefutation 6.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 157 expanded)
%              Number of leaves         :   41 (  70 expanded)
%              Depth                    :    6
%              Number of atoms          :  153 ( 406 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(A))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(B))
                       => ( r1_tarski(k7_relset_1(A,B,C,D),E)
                        <=> r1_tarski(D,k8_relset_1(A,B,C,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
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

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_36,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_82,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4770,plain,(
    ! [A_330,B_331,C_332,D_333] :
      ( k8_relset_1(A_330,B_331,C_332,D_333) = k10_relat_1(C_332,D_333)
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4780,plain,(
    ! [D_333] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_333) = k10_relat_1('#skF_4',D_333) ),
    inference(resolution,[status(thm)],[c_48,c_4770])).

tff(c_16,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_93,plain,(
    ! [B_77,A_78] :
      ( v1_relat_1(B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_78))
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_99,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_93])).

tff(c_113,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_99])).

tff(c_974,plain,(
    ! [A_136,B_137,C_138,D_139] :
      ( k8_relset_1(A_136,B_137,C_138,D_139) = k10_relat_1(C_138,D_139)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_984,plain,(
    ! [D_139] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_139) = k10_relat_1('#skF_4',D_139) ),
    inference(resolution,[status(thm)],[c_48,c_974])).

tff(c_58,plain,
    ( ~ r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6'))
    | ~ r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_117,plain,(
    ~ r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,
    ( r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_152,plain,(
    r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_64])).

tff(c_989,plain,(
    r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_152])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_18,plain,(
    ! [C_18,A_16,B_17] :
      ( r1_tarski(k9_relat_1(C_18,A_16),k9_relat_1(C_18,B_17))
      | ~ r1_tarski(A_16,B_17)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_273,plain,(
    ! [B_95,A_96] :
      ( r1_tarski(k9_relat_1(B_95,k10_relat_1(B_95,A_96)),A_96)
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2647,plain,(
    ! [A_233,A_234,B_235] :
      ( r1_tarski(A_233,A_234)
      | ~ r1_tarski(A_233,k9_relat_1(B_235,k10_relat_1(B_235,A_234)))
      | ~ v1_funct_1(B_235)
      | ~ v1_relat_1(B_235) ) ),
    inference(resolution,[status(thm)],[c_273,c_2])).

tff(c_3914,plain,(
    ! [C_283,A_284,A_285] :
      ( r1_tarski(k9_relat_1(C_283,A_284),A_285)
      | ~ v1_funct_1(C_283)
      | ~ r1_tarski(A_284,k10_relat_1(C_283,A_285))
      | ~ v1_relat_1(C_283) ) ),
    inference(resolution,[status(thm)],[c_18,c_2647])).

tff(c_671,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( k7_relset_1(A_120,B_121,C_122,D_123) = k9_relat_1(C_122,D_123)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_681,plain,(
    ! [D_123] : k7_relset_1('#skF_2','#skF_3','#skF_4',D_123) = k9_relat_1('#skF_4',D_123) ),
    inference(resolution,[status(thm)],[c_48,c_671])).

tff(c_683,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_117])).

tff(c_4015,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3914,c_683])).

tff(c_4081,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_989,c_52,c_4015])).

tff(c_4082,plain,(
    ~ r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_4782,plain,(
    ~ r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4780,c_4082])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_69,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(A_72,B_73)
      | ~ m1_subset_1(A_72,k1_zfmisc_1(B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_86,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_69])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4308,plain,(
    ! [A_304,B_305,C_306] :
      ( k1_relset_1(A_304,B_305,C_306) = k1_relat_1(C_306)
      | ~ m1_subset_1(C_306,k1_zfmisc_1(k2_zfmisc_1(A_304,B_305))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4321,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_4308])).

tff(c_5363,plain,(
    ! [B_358,A_359,C_360] :
      ( k1_xboole_0 = B_358
      | k1_relset_1(A_359,B_358,C_360) = A_359
      | ~ v1_funct_2(C_360,A_359,B_358)
      | ~ m1_subset_1(C_360,k1_zfmisc_1(k2_zfmisc_1(A_359,B_358))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_5370,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_5363])).

tff(c_5378,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4321,c_5370])).

tff(c_5380,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5378])).

tff(c_4918,plain,(
    ! [A_338,B_339,C_340,D_341] :
      ( k7_relset_1(A_338,B_339,C_340,D_341) = k9_relat_1(C_340,D_341)
      | ~ m1_subset_1(C_340,k1_zfmisc_1(k2_zfmisc_1(A_338,B_339))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4928,plain,(
    ! [D_341] : k7_relset_1('#skF_2','#skF_3','#skF_4',D_341) = k9_relat_1('#skF_4',D_341) ),
    inference(resolution,[status(thm)],[c_48,c_4918])).

tff(c_4083,plain,(
    r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_4935,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4928,c_4083])).

tff(c_5771,plain,(
    ! [A_378,C_379,B_380] :
      ( r1_tarski(A_378,k10_relat_1(C_379,B_380))
      | ~ r1_tarski(k9_relat_1(C_379,A_378),B_380)
      | ~ r1_tarski(A_378,k1_relat_1(C_379))
      | ~ v1_funct_1(C_379)
      | ~ v1_relat_1(C_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5789,plain,
    ( r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4935,c_5771])).

tff(c_5813,plain,(
    r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_52,c_86,c_5380,c_5789])).

tff(c_5815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4782,c_5813])).

tff(c_5816,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5378])).

tff(c_6,plain,(
    ! [A_5] : m1_subset_1('#skF_1'(A_5),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4124,plain,(
    ! [A_289,B_290] :
      ( r2_hidden(A_289,B_290)
      | v1_xboole_0(B_290)
      | ~ m1_subset_1(A_289,B_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    ! [B_25,A_24] :
      ( ~ r1_tarski(B_25,A_24)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4129,plain,(
    ! [B_291,A_292] :
      ( ~ r1_tarski(B_291,A_292)
      | v1_xboole_0(B_291)
      | ~ m1_subset_1(A_292,B_291) ) ),
    inference(resolution,[status(thm)],[c_4124,c_24])).

tff(c_4153,plain,(
    ! [A_4] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_4129])).

tff(c_4188,plain,(
    ! [A_297] : ~ m1_subset_1(A_297,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_4153])).

tff(c_4193,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_4188])).

tff(c_4194,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4153])).

tff(c_5833,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5816,c_4194])).

tff(c_5837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5833])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:31:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.22/2.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.22/2.23  
% 6.22/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.22/2.24  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 6.22/2.24  
% 6.22/2.24  %Foreground sorts:
% 6.22/2.24  
% 6.22/2.24  
% 6.22/2.24  %Background operators:
% 6.22/2.24  
% 6.22/2.24  
% 6.22/2.24  %Foreground operators:
% 6.22/2.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.22/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.22/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.22/2.24  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 6.22/2.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.22/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.22/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.22/2.24  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.22/2.24  tff('#skF_5', type, '#skF_5': $i).
% 6.22/2.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.22/2.24  tff('#skF_6', type, '#skF_6': $i).
% 6.22/2.24  tff('#skF_2', type, '#skF_2': $i).
% 6.22/2.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.22/2.24  tff('#skF_3', type, '#skF_3': $i).
% 6.22/2.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.22/2.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.22/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.22/2.24  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.22/2.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.22/2.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.22/2.24  tff('#skF_4', type, '#skF_4': $i).
% 6.22/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.22/2.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.22/2.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.22/2.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.22/2.24  
% 6.22/2.25  tff(f_137, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_2)).
% 6.22/2.25  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 6.22/2.25  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.22/2.25  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.22/2.25  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 6.22/2.25  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 6.22/2.25  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.22/2.25  tff(f_90, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.22/2.25  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.22/2.25  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.22/2.25  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.22/2.25  tff(f_77, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 6.22/2.25  tff(f_36, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 6.22/2.25  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.22/2.25  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 6.22/2.25  tff(f_82, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.22/2.25  tff(c_54, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.22/2.25  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.22/2.25  tff(c_4770, plain, (![A_330, B_331, C_332, D_333]: (k8_relset_1(A_330, B_331, C_332, D_333)=k10_relat_1(C_332, D_333) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.22/2.25  tff(c_4780, plain, (![D_333]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_333)=k10_relat_1('#skF_4', D_333))), inference(resolution, [status(thm)], [c_48, c_4770])).
% 6.22/2.25  tff(c_16, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.22/2.25  tff(c_93, plain, (![B_77, A_78]: (v1_relat_1(B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(A_78)) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.22/2.25  tff(c_99, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_93])).
% 6.22/2.25  tff(c_113, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_99])).
% 6.22/2.25  tff(c_974, plain, (![A_136, B_137, C_138, D_139]: (k8_relset_1(A_136, B_137, C_138, D_139)=k10_relat_1(C_138, D_139) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.22/2.25  tff(c_984, plain, (![D_139]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_139)=k10_relat_1('#skF_4', D_139))), inference(resolution, [status(thm)], [c_48, c_974])).
% 6.22/2.25  tff(c_58, plain, (~r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')) | ~r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.22/2.25  tff(c_117, plain, (~r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_58])).
% 6.22/2.25  tff(c_64, plain, (r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.22/2.25  tff(c_152, plain, (r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_117, c_64])).
% 6.22/2.25  tff(c_989, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_984, c_152])).
% 6.22/2.25  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.22/2.25  tff(c_18, plain, (![C_18, A_16, B_17]: (r1_tarski(k9_relat_1(C_18, A_16), k9_relat_1(C_18, B_17)) | ~r1_tarski(A_16, B_17) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.22/2.25  tff(c_273, plain, (![B_95, A_96]: (r1_tarski(k9_relat_1(B_95, k10_relat_1(B_95, A_96)), A_96) | ~v1_funct_1(B_95) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.22/2.25  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.22/2.25  tff(c_2647, plain, (![A_233, A_234, B_235]: (r1_tarski(A_233, A_234) | ~r1_tarski(A_233, k9_relat_1(B_235, k10_relat_1(B_235, A_234))) | ~v1_funct_1(B_235) | ~v1_relat_1(B_235))), inference(resolution, [status(thm)], [c_273, c_2])).
% 6.22/2.25  tff(c_3914, plain, (![C_283, A_284, A_285]: (r1_tarski(k9_relat_1(C_283, A_284), A_285) | ~v1_funct_1(C_283) | ~r1_tarski(A_284, k10_relat_1(C_283, A_285)) | ~v1_relat_1(C_283))), inference(resolution, [status(thm)], [c_18, c_2647])).
% 6.22/2.25  tff(c_671, plain, (![A_120, B_121, C_122, D_123]: (k7_relset_1(A_120, B_121, C_122, D_123)=k9_relat_1(C_122, D_123) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.22/2.25  tff(c_681, plain, (![D_123]: (k7_relset_1('#skF_2', '#skF_3', '#skF_4', D_123)=k9_relat_1('#skF_4', D_123))), inference(resolution, [status(thm)], [c_48, c_671])).
% 6.22/2.25  tff(c_683, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_681, c_117])).
% 6.22/2.25  tff(c_4015, plain, (~v1_funct_1('#skF_4') | ~r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3914, c_683])).
% 6.22/2.25  tff(c_4081, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_989, c_52, c_4015])).
% 6.22/2.25  tff(c_4082, plain, (~r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_58])).
% 6.22/2.25  tff(c_4782, plain, (~r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4780, c_4082])).
% 6.22/2.25  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.22/2.25  tff(c_69, plain, (![A_72, B_73]: (r1_tarski(A_72, B_73) | ~m1_subset_1(A_72, k1_zfmisc_1(B_73)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.22/2.25  tff(c_86, plain, (r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_69])).
% 6.22/2.25  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.22/2.25  tff(c_4308, plain, (![A_304, B_305, C_306]: (k1_relset_1(A_304, B_305, C_306)=k1_relat_1(C_306) | ~m1_subset_1(C_306, k1_zfmisc_1(k2_zfmisc_1(A_304, B_305))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.22/2.25  tff(c_4321, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_4308])).
% 6.22/2.25  tff(c_5363, plain, (![B_358, A_359, C_360]: (k1_xboole_0=B_358 | k1_relset_1(A_359, B_358, C_360)=A_359 | ~v1_funct_2(C_360, A_359, B_358) | ~m1_subset_1(C_360, k1_zfmisc_1(k2_zfmisc_1(A_359, B_358))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.22/2.25  tff(c_5370, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_5363])).
% 6.22/2.25  tff(c_5378, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4321, c_5370])).
% 6.22/2.25  tff(c_5380, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_5378])).
% 6.22/2.25  tff(c_4918, plain, (![A_338, B_339, C_340, D_341]: (k7_relset_1(A_338, B_339, C_340, D_341)=k9_relat_1(C_340, D_341) | ~m1_subset_1(C_340, k1_zfmisc_1(k2_zfmisc_1(A_338, B_339))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.22/2.25  tff(c_4928, plain, (![D_341]: (k7_relset_1('#skF_2', '#skF_3', '#skF_4', D_341)=k9_relat_1('#skF_4', D_341))), inference(resolution, [status(thm)], [c_48, c_4918])).
% 6.22/2.25  tff(c_4083, plain, (r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 6.22/2.25  tff(c_4935, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4928, c_4083])).
% 6.22/2.25  tff(c_5771, plain, (![A_378, C_379, B_380]: (r1_tarski(A_378, k10_relat_1(C_379, B_380)) | ~r1_tarski(k9_relat_1(C_379, A_378), B_380) | ~r1_tarski(A_378, k1_relat_1(C_379)) | ~v1_funct_1(C_379) | ~v1_relat_1(C_379))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.22/2.25  tff(c_5789, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4935, c_5771])).
% 6.22/2.25  tff(c_5813, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_52, c_86, c_5380, c_5789])).
% 6.22/2.25  tff(c_5815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4782, c_5813])).
% 6.22/2.25  tff(c_5816, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_5378])).
% 6.22/2.25  tff(c_6, plain, (![A_5]: (m1_subset_1('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.22/2.25  tff(c_4, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.22/2.25  tff(c_4124, plain, (![A_289, B_290]: (r2_hidden(A_289, B_290) | v1_xboole_0(B_290) | ~m1_subset_1(A_289, B_290))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.22/2.25  tff(c_24, plain, (![B_25, A_24]: (~r1_tarski(B_25, A_24) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.22/2.25  tff(c_4129, plain, (![B_291, A_292]: (~r1_tarski(B_291, A_292) | v1_xboole_0(B_291) | ~m1_subset_1(A_292, B_291))), inference(resolution, [status(thm)], [c_4124, c_24])).
% 6.22/2.25  tff(c_4153, plain, (![A_4]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_4129])).
% 6.22/2.25  tff(c_4188, plain, (![A_297]: (~m1_subset_1(A_297, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_4153])).
% 6.22/2.25  tff(c_4193, plain, $false, inference(resolution, [status(thm)], [c_6, c_4188])).
% 6.22/2.25  tff(c_4194, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_4153])).
% 6.22/2.25  tff(c_5833, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5816, c_4194])).
% 6.22/2.25  tff(c_5837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_5833])).
% 6.22/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.22/2.25  
% 6.22/2.25  Inference rules
% 6.22/2.25  ----------------------
% 6.22/2.25  #Ref     : 0
% 6.22/2.25  #Sup     : 1207
% 6.22/2.25  #Fact    : 0
% 6.22/2.25  #Define  : 0
% 6.22/2.25  #Split   : 45
% 6.22/2.25  #Chain   : 0
% 6.22/2.25  #Close   : 0
% 6.22/2.25  
% 6.22/2.25  Ordering : KBO
% 6.22/2.25  
% 6.22/2.25  Simplification rules
% 6.22/2.25  ----------------------
% 6.22/2.25  #Subsume      : 189
% 6.22/2.25  #Demod        : 508
% 6.22/2.25  #Tautology    : 325
% 6.22/2.25  #SimpNegUnit  : 34
% 6.22/2.25  #BackRed      : 87
% 6.22/2.25  
% 6.22/2.25  #Partial instantiations: 0
% 6.22/2.25  #Strategies tried      : 1
% 6.22/2.25  
% 6.22/2.25  Timing (in seconds)
% 6.22/2.25  ----------------------
% 6.22/2.26  Preprocessing        : 0.33
% 6.22/2.26  Parsing              : 0.17
% 6.22/2.26  CNF conversion       : 0.03
% 6.22/2.26  Main loop            : 1.11
% 6.22/2.26  Inferencing          : 0.35
% 6.22/2.26  Reduction            : 0.40
% 6.22/2.26  Demodulation         : 0.29
% 6.22/2.26  BG Simplification    : 0.04
% 6.22/2.26  Subsumption          : 0.22
% 6.22/2.26  Abstraction          : 0.06
% 6.22/2.26  MUC search           : 0.00
% 6.22/2.26  Cooper               : 0.00
% 6.22/2.26  Total                : 1.48
% 6.22/2.26  Index Insertion      : 0.00
% 6.22/2.26  Index Deletion       : 0.00
% 6.22/2.26  Index Matching       : 0.00
% 6.22/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
