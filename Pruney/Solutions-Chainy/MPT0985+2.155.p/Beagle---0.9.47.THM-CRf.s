%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:51 EST 2020

% Result     : Theorem 8.73s
% Output     : CNFRefutation 9.13s
% Verified   : 
% Statistics : Number of formulae       :  327 (5212 expanded)
%              Number of leaves         :   38 (1780 expanded)
%              Depth                    :   16
%              Number of atoms          :  684 (17042 expanded)
%              Number of equality atoms :  197 (5329 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_137,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_153,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_159,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_153])).

tff(c_163,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_159])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_56,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_11227,plain,(
    ! [A_1076,B_1077,C_1078] :
      ( k2_relset_1(A_1076,B_1077,C_1078) = k2_relat_1(C_1078)
      | ~ m1_subset_1(C_1078,k1_zfmisc_1(k2_zfmisc_1(A_1076,B_1077))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_11237,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_11227])).

tff(c_11241,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_11237])).

tff(c_26,plain,(
    ! [A_14] :
      ( k1_relat_1(k2_funct_1(A_14)) = k2_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_224,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relset_1(A_62,B_63,C_64) = k1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_233,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_224])).

tff(c_6240,plain,(
    ! [B_640,A_641,C_642] :
      ( k1_xboole_0 = B_640
      | k1_relset_1(A_641,B_640,C_642) = A_641
      | ~ v1_funct_2(C_642,A_641,B_640)
      | ~ m1_subset_1(C_642,k1_zfmisc_1(k2_zfmisc_1(A_641,B_640))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6258,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_6240])).

tff(c_6266,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_233,c_6258])).

tff(c_6267,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_6266])).

tff(c_24,plain,(
    ! [A_14] :
      ( k2_relat_1(k2_funct_1(A_14)) = k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_85,plain,(
    ! [A_43] :
      ( v1_funct_1(k2_funct_1(A_43))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_54,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_78,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_88,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_85,c_78])).

tff(c_91,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_88])).

tff(c_118,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_124,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_118])).

tff(c_128,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_124])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_128])).

tff(c_132,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_277,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_284,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_277])).

tff(c_287,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_284])).

tff(c_309,plain,(
    ! [B_80,A_81] :
      ( v1_funct_2(B_80,k1_relat_1(B_80),A_81)
      | ~ r1_tarski(k2_relat_1(B_80),A_81)
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_7747,plain,(
    ! [A_793,A_794] :
      ( v1_funct_2(k2_funct_1(A_793),k2_relat_1(A_793),A_794)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_793)),A_794)
      | ~ v1_funct_1(k2_funct_1(A_793))
      | ~ v1_relat_1(k2_funct_1(A_793))
      | ~ v2_funct_1(A_793)
      | ~ v1_funct_1(A_793)
      | ~ v1_relat_1(A_793) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_309])).

tff(c_7750,plain,(
    ! [A_794] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_794)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_794)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_7747])).

tff(c_7755,plain,(
    ! [A_794] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_794)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_794)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_132,c_7750])).

tff(c_7756,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7755])).

tff(c_7759,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_7756])).

tff(c_7763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_7759])).

tff(c_7765,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7755])).

tff(c_2494,plain,(
    ! [B_322,A_323] :
      ( m1_subset_1(B_322,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_322),A_323)))
      | ~ r1_tarski(k2_relat_1(B_322),A_323)
      | ~ v1_funct_1(B_322)
      | ~ v1_relat_1(B_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_7835,plain,(
    ! [A_801,A_802] :
      ( m1_subset_1(k2_funct_1(A_801),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_801),A_802)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_801)),A_802)
      | ~ v1_funct_1(k2_funct_1(A_801))
      | ~ v1_relat_1(k2_funct_1(A_801))
      | ~ v2_funct_1(A_801)
      | ~ v1_funct_1(A_801)
      | ~ v1_relat_1(A_801) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2494])).

tff(c_7866,plain,(
    ! [A_802] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_802)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_802)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_7835])).

tff(c_7911,plain,(
    ! [A_805] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_805)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_805) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_7765,c_132,c_7866])).

tff(c_131,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_192,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_7951,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_7911,c_192])).

tff(c_7958,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_7951])).

tff(c_7961,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_6,c_6267,c_7958])).

tff(c_7963,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6266])).

tff(c_73,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_77,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_73])).

tff(c_7962,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_6266])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_329,plain,(
    ! [C_86,A_87] :
      ( k1_xboole_0 = C_86
      | ~ v1_funct_2(C_86,A_87,k1_xboole_0)
      | k1_xboole_0 = A_87
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_334,plain,(
    ! [A_4,A_87] :
      ( k1_xboole_0 = A_4
      | ~ v1_funct_2(A_4,A_87,k1_xboole_0)
      | k1_xboole_0 = A_87
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_87,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_12,c_329])).

tff(c_9380,plain,(
    ! [A_917,A_918] :
      ( A_917 = '#skF_2'
      | ~ v1_funct_2(A_917,A_918,'#skF_2')
      | A_918 = '#skF_2'
      | ~ r1_tarski(A_917,k2_zfmisc_1(A_918,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7962,c_7962,c_7962,c_7962,c_334])).

tff(c_9395,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_77,c_9380])).

tff(c_9405,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_9395])).

tff(c_9407,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9405])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_7980,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7962,c_8])).

tff(c_348,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( k7_relset_1(A_91,B_92,C_93,D_94) = k9_relat_1(C_93,D_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_355,plain,(
    ! [D_94] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_94) = k9_relat_1('#skF_3',D_94) ),
    inference(resolution,[status(thm)],[c_60,c_348])).

tff(c_387,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( m1_subset_1(k7_relset_1(A_103,B_104,C_105,D_106),k1_zfmisc_1(B_104))
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_414,plain,(
    ! [D_94] :
      ( m1_subset_1(k9_relat_1('#skF_3',D_94),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_387])).

tff(c_423,plain,(
    ! [D_107] : m1_subset_1(k9_relat_1('#skF_3',D_107),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_414])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_432,plain,(
    ! [D_108] : r1_tarski(k9_relat_1('#skF_3',D_108),'#skF_2') ),
    inference(resolution,[status(thm)],[c_423,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_439,plain,(
    ! [D_108] :
      ( k9_relat_1('#skF_3',D_108) = '#skF_2'
      | ~ r1_tarski('#skF_2',k9_relat_1('#skF_3',D_108)) ) ),
    inference(resolution,[status(thm)],[c_432,c_2])).

tff(c_7987,plain,(
    ! [D_108] : k9_relat_1('#skF_3',D_108) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7980,c_439])).

tff(c_2679,plain,(
    ! [B_335,A_336] :
      ( k10_relat_1(B_335,k9_relat_1(B_335,A_336)) = A_336
      | ~ v2_funct_1(B_335)
      | ~ r1_tarski(A_336,k1_relat_1(B_335))
      | ~ v1_funct_1(B_335)
      | ~ v1_relat_1(B_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2689,plain,(
    ! [B_335] :
      ( k10_relat_1(B_335,k9_relat_1(B_335,k1_xboole_0)) = k1_xboole_0
      | ~ v2_funct_1(B_335)
      | ~ v1_funct_1(B_335)
      | ~ v1_relat_1(B_335) ) ),
    inference(resolution,[status(thm)],[c_8,c_2679])).

tff(c_8153,plain,(
    ! [B_819] :
      ( k10_relat_1(B_819,k9_relat_1(B_819,'#skF_2')) = '#skF_2'
      | ~ v2_funct_1(B_819)
      | ~ v1_funct_1(B_819)
      | ~ v1_relat_1(B_819) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7962,c_7962,c_2689])).

tff(c_8167,plain,
    ( k10_relat_1('#skF_3','#skF_2') = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7987,c_8153])).

tff(c_8173,plain,(
    k10_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_8167])).

tff(c_9419,plain,(
    k10_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9407,c_9407,c_8173])).

tff(c_9429,plain,(
    ! [D_108] : k9_relat_1('#skF_3',D_108) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9407,c_7987])).

tff(c_9596,plain,(
    ! [B_928] :
      ( k10_relat_1(B_928,k9_relat_1(B_928,k1_relat_1(B_928))) = k1_relat_1(B_928)
      | ~ v2_funct_1(B_928)
      | ~ v1_funct_1(B_928)
      | ~ v1_relat_1(B_928) ) ),
    inference(resolution,[status(thm)],[c_6,c_2679])).

tff(c_9610,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9429,c_9596])).

tff(c_9622,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_9419,c_9610])).

tff(c_9624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7963,c_9622])).

tff(c_9625,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9405])).

tff(c_9650,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9625,c_7980])).

tff(c_2701,plain,(
    ! [B_338,A_339,C_340] :
      ( k1_xboole_0 = B_338
      | k1_relset_1(A_339,B_338,C_340) = A_339
      | ~ v1_funct_2(C_340,A_339,B_338)
      | ~ m1_subset_1(C_340,k1_zfmisc_1(k2_zfmisc_1(A_339,B_338))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2719,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_2701])).

tff(c_2727,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_233,c_2719])).

tff(c_2728,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2727])).

tff(c_4195,plain,(
    ! [A_495,A_496] :
      ( v1_funct_2(k2_funct_1(A_495),k2_relat_1(A_495),A_496)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_495)),A_496)
      | ~ v1_funct_1(k2_funct_1(A_495))
      | ~ v1_relat_1(k2_funct_1(A_495))
      | ~ v2_funct_1(A_495)
      | ~ v1_funct_1(A_495)
      | ~ v1_relat_1(A_495) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_309])).

tff(c_4198,plain,(
    ! [A_496] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_496)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_496)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_4195])).

tff(c_4203,plain,(
    ! [A_496] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_496)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_496)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_132,c_4198])).

tff(c_4204,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4203])).

tff(c_4207,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_4204])).

tff(c_4211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_4207])).

tff(c_4213,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4203])).

tff(c_4274,plain,(
    ! [A_503,A_504] :
      ( m1_subset_1(k2_funct_1(A_503),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_503),A_504)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_503)),A_504)
      | ~ v1_funct_1(k2_funct_1(A_503))
      | ~ v1_relat_1(k2_funct_1(A_503))
      | ~ v2_funct_1(A_503)
      | ~ v1_funct_1(A_503)
      | ~ v1_relat_1(A_503) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2494])).

tff(c_4305,plain,(
    ! [A_504] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_504)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_504)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_4274])).

tff(c_4350,plain,(
    ! [A_507] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_507)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_507) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_4213,c_132,c_4305])).

tff(c_4390,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_4350,c_192])).

tff(c_4397,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4390])).

tff(c_4400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_6,c_2728,c_4397])).

tff(c_4401,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2727])).

tff(c_5773,plain,(
    ! [A_617,A_618] :
      ( A_617 = '#skF_2'
      | ~ v1_funct_2(A_617,A_618,'#skF_2')
      | A_618 = '#skF_2'
      | ~ r1_tarski(A_617,k2_zfmisc_1(A_618,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4401,c_4401,c_4401,c_4401,c_334])).

tff(c_5788,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_77,c_5773])).

tff(c_5799,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5788])).

tff(c_5801,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5799])).

tff(c_238,plain,(
    ! [A_65,B_66,A_67] :
      ( k1_relset_1(A_65,B_66,A_67) = k1_relat_1(A_67)
      | ~ r1_tarski(A_67,k2_zfmisc_1(A_65,B_66)) ) ),
    inference(resolution,[status(thm)],[c_12,c_224])).

tff(c_253,plain,(
    ! [A_65,B_66] : k1_relset_1(A_65,B_66,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_238])).

tff(c_365,plain,(
    ! [A_96,B_97,A_98,D_99] :
      ( k7_relset_1(A_96,B_97,A_98,D_99) = k9_relat_1(A_98,D_99)
      | ~ r1_tarski(A_98,k2_zfmisc_1(A_96,B_97)) ) ),
    inference(resolution,[status(thm)],[c_12,c_348])).

tff(c_377,plain,(
    ! [A_96,B_97,D_99] : k7_relset_1(A_96,B_97,k1_xboole_0,D_99) = k9_relat_1(k1_xboole_0,D_99) ),
    inference(resolution,[status(thm)],[c_8,c_365])).

tff(c_2487,plain,(
    ! [D_319,B_320,A_321] :
      ( m1_subset_1(k9_relat_1(k1_xboole_0,D_319),k1_zfmisc_1(B_320))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_321,B_320))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_387])).

tff(c_2490,plain,(
    ! [D_319,B_320,A_321] :
      ( m1_subset_1(k9_relat_1(k1_xboole_0,D_319),k1_zfmisc_1(B_320))
      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(A_321,B_320)) ) ),
    inference(resolution,[status(thm)],[c_12,c_2487])).

tff(c_2531,plain,(
    ! [D_324,B_325] : m1_subset_1(k9_relat_1(k1_xboole_0,D_324),k1_zfmisc_1(B_325)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2490])).

tff(c_2564,plain,(
    ! [D_326,B_327] : r1_tarski(k9_relat_1(k1_xboole_0,D_326),B_327) ),
    inference(resolution,[status(thm)],[c_2531,c_10])).

tff(c_140,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ r1_tarski(B_53,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_152,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_140])).

tff(c_2594,plain,(
    ! [D_326] : k9_relat_1(k1_xboole_0,D_326) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2564,c_152])).

tff(c_2493,plain,(
    ! [D_319,B_320] : m1_subset_1(k9_relat_1(k1_xboole_0,D_319),k1_zfmisc_1(B_320)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2490])).

tff(c_2607,plain,(
    ! [B_329] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(B_329)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2594,c_2493])).

tff(c_44,plain,(
    ! [B_30,C_31] :
      ( k1_relset_1(k1_xboole_0,B_30,C_31) = k1_xboole_0
      | ~ v1_funct_2(C_31,k1_xboole_0,B_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2611,plain,(
    ! [B_30] :
      ( k1_relset_1(k1_xboole_0,B_30,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,B_30) ) ),
    inference(resolution,[status(thm)],[c_2607,c_44])).

tff(c_2634,plain,(
    ! [B_30] :
      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_2611])).

tff(c_2690,plain,(
    ! [B_30] : ~ v1_funct_2(k1_xboole_0,k1_xboole_0,B_30) ),
    inference(splitLeft,[status(thm)],[c_2634])).

tff(c_2597,plain,(
    ! [B_320] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(B_320)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2594,c_2493])).

tff(c_2648,plain,(
    ! [C_330,B_331] :
      ( v1_funct_2(C_330,k1_xboole_0,B_331)
      | k1_relset_1(k1_xboole_0,B_331,C_330) != k1_xboole_0
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_331))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2652,plain,(
    ! [B_331] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_331)
      | k1_relset_1(k1_xboole_0,B_331,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2597,c_2648])).

tff(c_2662,plain,(
    ! [B_331] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_331)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_2652])).

tff(c_2698,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2690,c_2662])).

tff(c_4404,plain,(
    k1_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4401,c_4401,c_2698])).

tff(c_5823,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5801,c_5801,c_4404])).

tff(c_14,plain,(
    ! [B_8,A_6] :
      ( v1_relat_1(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_430,plain,(
    ! [D_107] :
      ( v1_relat_1(k9_relat_1('#skF_3',D_107))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_423,c_14])).

tff(c_440,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_430])).

tff(c_679,plain,(
    ! [B_134,A_135,C_136] :
      ( k1_xboole_0 = B_134
      | k1_relset_1(A_135,B_134,C_136) = A_135
      | ~ v1_funct_2(C_136,A_135,B_134)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_135,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_697,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_679])).

tff(c_705,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_233,c_697])).

tff(c_706,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_705])).

tff(c_2229,plain,(
    ! [A_297,A_298] :
      ( v1_funct_2(k2_funct_1(A_297),k2_relat_1(A_297),A_298)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_297)),A_298)
      | ~ v1_funct_1(k2_funct_1(A_297))
      | ~ v1_relat_1(k2_funct_1(A_297))
      | ~ v2_funct_1(A_297)
      | ~ v1_funct_1(A_297)
      | ~ v1_relat_1(A_297) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_309])).

tff(c_2232,plain,(
    ! [A_298] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_298)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_298)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_2229])).

tff(c_2237,plain,(
    ! [A_298] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_298)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_298)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_132,c_2232])).

tff(c_2238,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2237])).

tff(c_2241,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_2238])).

tff(c_2245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_2241])).

tff(c_2247,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2237])).

tff(c_472,plain,(
    ! [B_118,A_119] :
      ( m1_subset_1(B_118,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_118),A_119)))
      | ~ r1_tarski(k2_relat_1(B_118),A_119)
      | ~ v1_funct_1(B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2328,plain,(
    ! [A_308,A_309] :
      ( m1_subset_1(k2_funct_1(A_308),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_308),A_309)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_308)),A_309)
      | ~ v1_funct_1(k2_funct_1(A_308))
      | ~ v1_relat_1(k2_funct_1(A_308))
      | ~ v2_funct_1(A_308)
      | ~ v1_funct_1(A_308)
      | ~ v1_relat_1(A_308) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_472])).

tff(c_2359,plain,(
    ! [A_309] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_309)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_309)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_2328])).

tff(c_2386,plain,(
    ! [A_311] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_311)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_311) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_2247,c_132,c_2359])).

tff(c_2426,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2386,c_192])).

tff(c_2433,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2426])).

tff(c_2436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_6,c_706,c_2433])).

tff(c_2437,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_705])).

tff(c_177,plain,(
    ! [A_58,B_59] :
      ( v1_relat_1(A_58)
      | ~ v1_relat_1(B_59)
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_12,c_153])).

tff(c_191,plain,(
    ! [A_3] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_3) ) ),
    inference(resolution,[status(thm)],[c_8,c_177])).

tff(c_193,plain,(
    ! [A_3] : ~ v1_relat_1(A_3) ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_163])).

tff(c_200,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_2453,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_200])).

tff(c_2457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_440,c_2453])).

tff(c_2459,plain,(
    v1_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_430])).

tff(c_5826,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5801,c_2459])).

tff(c_4402,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2727])).

tff(c_4768,plain,(
    ! [A_545,A_546] :
      ( A_545 = '#skF_2'
      | ~ v1_funct_2(A_545,A_546,'#skF_2')
      | A_546 = '#skF_2'
      | ~ r1_tarski(A_545,k2_zfmisc_1(A_546,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4401,c_4401,c_4401,c_4401,c_334])).

tff(c_4783,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_77,c_4768])).

tff(c_4794,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4783])).

tff(c_4796,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4794])).

tff(c_4419,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4401,c_8])).

tff(c_4426,plain,(
    ! [D_108] : k9_relat_1('#skF_3',D_108) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4419,c_439])).

tff(c_4580,plain,(
    ! [B_521] :
      ( k10_relat_1(B_521,k9_relat_1(B_521,'#skF_2')) = '#skF_2'
      | ~ v2_funct_1(B_521)
      | ~ v1_funct_1(B_521)
      | ~ v1_relat_1(B_521) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4401,c_4401,c_2689])).

tff(c_4594,plain,
    ( k10_relat_1('#skF_3','#skF_2') = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4426,c_4580])).

tff(c_4600,plain,(
    k10_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_4594])).

tff(c_4803,plain,(
    k10_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4796,c_4796,c_4600])).

tff(c_4813,plain,(
    ! [D_108] : k9_relat_1('#skF_3',D_108) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4796,c_4426])).

tff(c_4991,plain,(
    ! [B_555] :
      ( k10_relat_1(B_555,k9_relat_1(B_555,k1_relat_1(B_555))) = k1_relat_1(B_555)
      | ~ v2_funct_1(B_555)
      | ~ v1_funct_1(B_555)
      | ~ v1_relat_1(B_555) ) ),
    inference(resolution,[status(thm)],[c_6,c_2679])).

tff(c_5005,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4813,c_4991])).

tff(c_5014,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_4803,c_5005])).

tff(c_5016,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4402,c_5014])).

tff(c_5017,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4794])).

tff(c_4409,plain,(
    ! [D_326] : k9_relat_1('#skF_2',D_326) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4401,c_4401,c_2594])).

tff(c_4590,plain,
    ( k10_relat_1('#skF_2','#skF_2') = '#skF_2'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4409,c_4580])).

tff(c_4598,plain,
    ( k10_relat_1('#skF_2','#skF_2') = '#skF_2'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2459,c_4590])).

tff(c_4629,plain,(
    ~ v1_funct_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4598])).

tff(c_5022,plain,(
    ~ v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5017,c_4629])).

tff(c_5051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5022])).

tff(c_5053,plain,(
    v1_funct_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4598])).

tff(c_5809,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5801,c_5053])).

tff(c_5256,plain,(
    ! [A_582,A_583] :
      ( A_582 = '#skF_2'
      | ~ v1_funct_2(A_582,A_583,'#skF_2')
      | A_583 = '#skF_2'
      | ~ r1_tarski(A_582,k2_zfmisc_1(A_583,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4401,c_4401,c_4401,c_4401,c_334])).

tff(c_5271,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_77,c_5256])).

tff(c_5282,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5271])).

tff(c_5284,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5282])).

tff(c_5296,plain,(
    k10_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5284,c_5284,c_4600])).

tff(c_5371,plain,(
    ! [D_586] : k9_relat_1('#skF_3',D_586) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5284,c_4426])).

tff(c_2688,plain,(
    ! [B_335] :
      ( k10_relat_1(B_335,k9_relat_1(B_335,k1_relat_1(B_335))) = k1_relat_1(B_335)
      | ~ v2_funct_1(B_335)
      | ~ v1_funct_1(B_335)
      | ~ v1_relat_1(B_335) ) ),
    inference(resolution,[status(thm)],[c_6,c_2679])).

tff(c_5377,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5371,c_2688])).

tff(c_5382,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_5377])).

tff(c_5539,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5296,c_5382])).

tff(c_5540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4402,c_5539])).

tff(c_5541,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5282])).

tff(c_5052,plain,
    ( ~ v2_funct_1('#skF_2')
    | k10_relat_1('#skF_2','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4598])).

tff(c_5054,plain,(
    ~ v2_funct_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_5052])).

tff(c_5550,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5541,c_5054])).

tff(c_5580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_5550])).

tff(c_5582,plain,(
    v2_funct_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_5052])).

tff(c_5808,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5801,c_5582])).

tff(c_5581,plain,(
    k10_relat_1('#skF_2','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5052])).

tff(c_5807,plain,(
    k10_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5801,c_5801,c_5801,c_5581])).

tff(c_5820,plain,(
    ! [D_326] : k9_relat_1('#skF_1',D_326) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5801,c_5801,c_4409])).

tff(c_5982,plain,(
    ! [B_626] :
      ( k10_relat_1(B_626,k9_relat_1(B_626,k1_relat_1(B_626))) = k1_relat_1(B_626)
      | ~ v2_funct_1(B_626)
      | ~ v1_funct_1(B_626)
      | ~ v1_relat_1(B_626) ) ),
    inference(resolution,[status(thm)],[c_6,c_2679])).

tff(c_5992,plain,
    ( k10_relat_1('#skF_1','#skF_1') = k1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5820,c_5982])).

tff(c_6003,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5826,c_5809,c_5808,c_5807,c_5992])).

tff(c_6005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5823,c_6003])).

tff(c_6006,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5799])).

tff(c_6029,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6006,c_6006,c_4404])).

tff(c_6018,plain,(
    k10_relat_1('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6006,c_6006,c_4600])).

tff(c_6028,plain,(
    ! [D_108] : k9_relat_1('#skF_3',D_108) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6006,c_4426])).

tff(c_6190,plain,(
    ! [B_636] :
      ( k10_relat_1(B_636,k9_relat_1(B_636,k1_relat_1(B_636))) = k1_relat_1(B_636)
      | ~ v2_funct_1(B_636)
      | ~ v1_funct_1(B_636)
      | ~ v1_relat_1(B_636) ) ),
    inference(resolution,[status(thm)],[c_6,c_2679])).

tff(c_6200,plain,
    ( k10_relat_1('#skF_3','#skF_3') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6028,c_6190])).

tff(c_6207,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_6018,c_6200])).

tff(c_6209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6029,c_6207])).

tff(c_6210,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2634])).

tff(c_7967,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7962,c_7962,c_6210])).

tff(c_9649,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9625,c_9625,c_7967])).

tff(c_9653,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9625,c_287])).

tff(c_10967,plain,(
    ! [A_1063,A_1064] :
      ( v1_funct_2(k2_funct_1(A_1063),k2_relat_1(A_1063),A_1064)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_1063)),A_1064)
      | ~ v1_funct_1(k2_funct_1(A_1063))
      | ~ v1_relat_1(k2_funct_1(A_1063))
      | ~ v2_funct_1(A_1063)
      | ~ v1_funct_1(A_1063)
      | ~ v1_relat_1(A_1063) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_309])).

tff(c_10970,plain,(
    ! [A_1064] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',A_1064)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_1064)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9653,c_10967])).

tff(c_10975,plain,(
    ! [A_1064] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',A_1064)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_1064)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_132,c_10970])).

tff(c_10976,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_10975])).

tff(c_10979,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_10976])).

tff(c_10983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_10979])).

tff(c_10985,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_10975])).

tff(c_11061,plain,(
    ! [A_1071,A_1072] :
      ( m1_subset_1(k2_funct_1(A_1071),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1071),A_1072)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_1071)),A_1072)
      | ~ v1_funct_1(k2_funct_1(A_1071))
      | ~ v1_relat_1(k2_funct_1(A_1071))
      | ~ v2_funct_1(A_1071)
      | ~ v1_funct_1(A_1071)
      | ~ v1_relat_1(A_1071) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2494])).

tff(c_11092,plain,(
    ! [A_1072] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_1072)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_1072)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9653,c_11061])).

tff(c_11110,plain,(
    ! [A_1073] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_1073)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_1073) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_10985,c_132,c_11092])).

tff(c_9657,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9625,c_192])).

tff(c_11162,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_11110,c_9657])).

tff(c_11174,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_11162])).

tff(c_11177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_9650,c_9649,c_11174])).

tff(c_11178,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_11179,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_11250,plain,(
    ! [A_1079,B_1080,C_1081] :
      ( k1_relset_1(A_1079,B_1080,C_1081) = k1_relat_1(C_1081)
      | ~ m1_subset_1(C_1081,k1_zfmisc_1(k2_zfmisc_1(A_1079,B_1080))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_11261,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_11179,c_11250])).

tff(c_13222,plain,(
    ! [B_1285,C_1286,A_1287] :
      ( k1_xboole_0 = B_1285
      | v1_funct_2(C_1286,A_1287,B_1285)
      | k1_relset_1(A_1287,B_1285,C_1286) != A_1287
      | ~ m1_subset_1(C_1286,k1_zfmisc_1(k2_zfmisc_1(A_1287,B_1285))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_13236,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_11179,c_13222])).

tff(c_13249,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11261,c_13236])).

tff(c_13250,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_11178,c_13249])).

tff(c_13255,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_13250])).

tff(c_13258,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_13255])).

tff(c_13261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_11241,c_13258])).

tff(c_13262,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13250])).

tff(c_13281,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13262,c_8])).

tff(c_11263,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_11250])).

tff(c_13164,plain,(
    ! [B_1281,A_1282,C_1283] :
      ( k1_xboole_0 = B_1281
      | k1_relset_1(A_1282,B_1281,C_1283) = A_1282
      | ~ v1_funct_2(C_1283,A_1282,B_1281)
      | ~ m1_subset_1(C_1283,k1_zfmisc_1(k2_zfmisc_1(A_1282,B_1281))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_13185,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_13164])).

tff(c_13195,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_11263,c_13185])).

tff(c_13196,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_13195])).

tff(c_11190,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_11179,c_14])).

tff(c_11196,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_11190])).

tff(c_13263,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_13250])).

tff(c_50,plain,(
    ! [B_33,A_32] :
      ( v1_funct_2(B_33,k1_relat_1(B_33),A_32)
      | ~ r1_tarski(k2_relat_1(B_33),A_32)
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_13296,plain,(
    ! [A_32] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_32)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_32)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13263,c_50])).

tff(c_13650,plain,(
    ! [A_1319] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_1319)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_1319) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11196,c_132,c_13296])).

tff(c_13653,plain,(
    ! [A_1319] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_1319)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_1319)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_13650])).

tff(c_13659,plain,(
    ! [A_1319] : v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_1319) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_13281,c_13196,c_13653])).

tff(c_13705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13659,c_11178])).

tff(c_13707,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13195])).

tff(c_13706,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_13195])).

tff(c_42,plain,(
    ! [B_30,C_31,A_29] :
      ( k1_xboole_0 = B_30
      | v1_funct_2(C_31,A_29,B_30)
      | k1_relset_1(A_29,B_30,C_31) != A_29
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_13772,plain,(
    ! [B_1324,C_1325,A_1326] :
      ( B_1324 = '#skF_2'
      | v1_funct_2(C_1325,A_1326,B_1324)
      | k1_relset_1(A_1326,B_1324,C_1325) != A_1326
      | ~ m1_subset_1(C_1325,k1_zfmisc_1(k2_zfmisc_1(A_1326,B_1324))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13706,c_42])).

tff(c_13782,plain,
    ( '#skF_2' = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_11179,c_13772])).

tff(c_13793,plain,
    ( '#skF_2' = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11261,c_13782])).

tff(c_13794,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_11178,c_13793])).

tff(c_13921,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_13794])).

tff(c_13924,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_13921])).

tff(c_13927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64,c_58,c_11241,c_13924])).

tff(c_13928,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13794])).

tff(c_13958,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13928,c_62])).

tff(c_13947,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13928,c_11263])).

tff(c_13955,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13928,c_77])).

tff(c_13943,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13928,c_13706])).

tff(c_13057,plain,(
    ! [B_1271,C_1272] :
      ( k1_relset_1(k1_xboole_0,B_1271,C_1272) = k1_xboole_0
      | ~ v1_funct_2(C_1272,k1_xboole_0,B_1271)
      | ~ m1_subset_1(C_1272,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_1271))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_13072,plain,(
    ! [B_1271,A_4] :
      ( k1_relset_1(k1_xboole_0,B_1271,A_4) = k1_xboole_0
      | ~ v1_funct_2(A_4,k1_xboole_0,B_1271)
      | ~ r1_tarski(A_4,k2_zfmisc_1(k1_xboole_0,B_1271)) ) ),
    inference(resolution,[status(thm)],[c_12,c_13057])).

tff(c_14277,plain,(
    ! [B_1361,A_1362] :
      ( k1_relset_1('#skF_1',B_1361,A_1362) = '#skF_1'
      | ~ v1_funct_2(A_1362,'#skF_1',B_1361)
      | ~ r1_tarski(A_1362,k2_zfmisc_1('#skF_1',B_1361)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13943,c_13943,c_13943,c_13943,c_13072])).

tff(c_14283,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_13955,c_14277])).

tff(c_14296,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13958,c_13947,c_14283])).

tff(c_14298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13707,c_14296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.73/3.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.80/3.26  
% 8.80/3.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.80/3.27  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.80/3.27  
% 8.80/3.27  %Foreground sorts:
% 8.80/3.27  
% 8.80/3.27  
% 8.80/3.27  %Background operators:
% 8.80/3.27  
% 8.80/3.27  
% 8.80/3.27  %Foreground operators:
% 8.80/3.27  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.80/3.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.80/3.27  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.80/3.27  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.80/3.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.80/3.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.80/3.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.80/3.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.80/3.27  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 8.80/3.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.80/3.27  tff('#skF_2', type, '#skF_2': $i).
% 8.80/3.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.80/3.27  tff('#skF_3', type, '#skF_3': $i).
% 8.80/3.27  tff('#skF_1', type, '#skF_1': $i).
% 8.80/3.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.80/3.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.80/3.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.80/3.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.80/3.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.80/3.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.80/3.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.80/3.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.80/3.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.80/3.27  
% 9.13/3.30  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.13/3.30  tff(f_137, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 9.13/3.30  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.13/3.30  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.13/3.30  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 9.13/3.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.13/3.30  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.13/3.30  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.13/3.30  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.13/3.30  tff(f_120, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 9.13/3.30  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.13/3.30  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.13/3.30  tff(f_90, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 9.13/3.30  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 9.13/3.30  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 9.13/3.30  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.13/3.30  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.13/3.30  tff(c_153, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.13/3.30  tff(c_159, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_153])).
% 9.13/3.30  tff(c_163, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_159])).
% 9.13/3.30  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.13/3.30  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.13/3.30  tff(c_56, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.13/3.30  tff(c_11227, plain, (![A_1076, B_1077, C_1078]: (k2_relset_1(A_1076, B_1077, C_1078)=k2_relat_1(C_1078) | ~m1_subset_1(C_1078, k1_zfmisc_1(k2_zfmisc_1(A_1076, B_1077))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.13/3.30  tff(c_11237, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_11227])).
% 9.13/3.30  tff(c_11241, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_11237])).
% 9.13/3.30  tff(c_26, plain, (![A_14]: (k1_relat_1(k2_funct_1(A_14))=k2_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.13/3.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.13/3.30  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.13/3.30  tff(c_224, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.13/3.30  tff(c_233, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_224])).
% 9.13/3.30  tff(c_6240, plain, (![B_640, A_641, C_642]: (k1_xboole_0=B_640 | k1_relset_1(A_641, B_640, C_642)=A_641 | ~v1_funct_2(C_642, A_641, B_640) | ~m1_subset_1(C_642, k1_zfmisc_1(k2_zfmisc_1(A_641, B_640))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.13/3.30  tff(c_6258, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_6240])).
% 9.13/3.30  tff(c_6266, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_233, c_6258])).
% 9.13/3.30  tff(c_6267, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_6266])).
% 9.13/3.30  tff(c_24, plain, (![A_14]: (k2_relat_1(k2_funct_1(A_14))=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.13/3.30  tff(c_20, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.13/3.30  tff(c_85, plain, (![A_43]: (v1_funct_1(k2_funct_1(A_43)) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.13/3.30  tff(c_54, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.13/3.30  tff(c_78, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_54])).
% 9.13/3.30  tff(c_88, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_85, c_78])).
% 9.13/3.30  tff(c_91, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_88])).
% 9.13/3.30  tff(c_118, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.13/3.30  tff(c_124, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_118])).
% 9.13/3.30  tff(c_128, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_124])).
% 9.13/3.30  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_128])).
% 9.13/3.30  tff(c_132, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_54])).
% 9.13/3.30  tff(c_277, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.13/3.30  tff(c_284, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_277])).
% 9.13/3.30  tff(c_287, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_284])).
% 9.13/3.30  tff(c_309, plain, (![B_80, A_81]: (v1_funct_2(B_80, k1_relat_1(B_80), A_81) | ~r1_tarski(k2_relat_1(B_80), A_81) | ~v1_funct_1(B_80) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.13/3.30  tff(c_7747, plain, (![A_793, A_794]: (v1_funct_2(k2_funct_1(A_793), k2_relat_1(A_793), A_794) | ~r1_tarski(k2_relat_1(k2_funct_1(A_793)), A_794) | ~v1_funct_1(k2_funct_1(A_793)) | ~v1_relat_1(k2_funct_1(A_793)) | ~v2_funct_1(A_793) | ~v1_funct_1(A_793) | ~v1_relat_1(A_793))), inference(superposition, [status(thm), theory('equality')], [c_26, c_309])).
% 9.13/3.30  tff(c_7750, plain, (![A_794]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_794) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_794) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_287, c_7747])).
% 9.13/3.30  tff(c_7755, plain, (![A_794]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_794) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_794) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_132, c_7750])).
% 9.13/3.30  tff(c_7756, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_7755])).
% 9.13/3.30  tff(c_7759, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_7756])).
% 9.13/3.30  tff(c_7763, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_7759])).
% 9.13/3.30  tff(c_7765, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_7755])).
% 9.13/3.30  tff(c_2494, plain, (![B_322, A_323]: (m1_subset_1(B_322, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_322), A_323))) | ~r1_tarski(k2_relat_1(B_322), A_323) | ~v1_funct_1(B_322) | ~v1_relat_1(B_322))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.13/3.30  tff(c_7835, plain, (![A_801, A_802]: (m1_subset_1(k2_funct_1(A_801), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_801), A_802))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_801)), A_802) | ~v1_funct_1(k2_funct_1(A_801)) | ~v1_relat_1(k2_funct_1(A_801)) | ~v2_funct_1(A_801) | ~v1_funct_1(A_801) | ~v1_relat_1(A_801))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2494])).
% 9.13/3.30  tff(c_7866, plain, (![A_802]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_802))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_802) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_287, c_7835])).
% 9.13/3.30  tff(c_7911, plain, (![A_805]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_805))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_805))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_7765, c_132, c_7866])).
% 9.13/3.30  tff(c_131, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_54])).
% 9.13/3.30  tff(c_192, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_131])).
% 9.13/3.30  tff(c_7951, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_7911, c_192])).
% 9.13/3.30  tff(c_7958, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_7951])).
% 9.13/3.30  tff(c_7961, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_6, c_6267, c_7958])).
% 9.13/3.30  tff(c_7963, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_6266])).
% 9.13/3.30  tff(c_73, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.13/3.30  tff(c_77, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_73])).
% 9.13/3.30  tff(c_7962, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_6266])).
% 9.13/3.30  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.13/3.30  tff(c_329, plain, (![C_86, A_87]: (k1_xboole_0=C_86 | ~v1_funct_2(C_86, A_87, k1_xboole_0) | k1_xboole_0=A_87 | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.13/3.30  tff(c_334, plain, (![A_4, A_87]: (k1_xboole_0=A_4 | ~v1_funct_2(A_4, A_87, k1_xboole_0) | k1_xboole_0=A_87 | ~r1_tarski(A_4, k2_zfmisc_1(A_87, k1_xboole_0)))), inference(resolution, [status(thm)], [c_12, c_329])).
% 9.13/3.30  tff(c_9380, plain, (![A_917, A_918]: (A_917='#skF_2' | ~v1_funct_2(A_917, A_918, '#skF_2') | A_918='#skF_2' | ~r1_tarski(A_917, k2_zfmisc_1(A_918, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_7962, c_7962, c_7962, c_7962, c_334])).
% 9.13/3.30  tff(c_9395, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_77, c_9380])).
% 9.13/3.30  tff(c_9405, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_9395])).
% 9.13/3.30  tff(c_9407, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_9405])).
% 9.13/3.30  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.13/3.30  tff(c_7980, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_7962, c_8])).
% 9.13/3.30  tff(c_348, plain, (![A_91, B_92, C_93, D_94]: (k7_relset_1(A_91, B_92, C_93, D_94)=k9_relat_1(C_93, D_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.13/3.30  tff(c_355, plain, (![D_94]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_94)=k9_relat_1('#skF_3', D_94))), inference(resolution, [status(thm)], [c_60, c_348])).
% 9.13/3.30  tff(c_387, plain, (![A_103, B_104, C_105, D_106]: (m1_subset_1(k7_relset_1(A_103, B_104, C_105, D_106), k1_zfmisc_1(B_104)) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.13/3.30  tff(c_414, plain, (![D_94]: (m1_subset_1(k9_relat_1('#skF_3', D_94), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_355, c_387])).
% 9.13/3.30  tff(c_423, plain, (![D_107]: (m1_subset_1(k9_relat_1('#skF_3', D_107), k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_414])).
% 9.13/3.30  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.13/3.30  tff(c_432, plain, (![D_108]: (r1_tarski(k9_relat_1('#skF_3', D_108), '#skF_2'))), inference(resolution, [status(thm)], [c_423, c_10])).
% 9.13/3.30  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.13/3.30  tff(c_439, plain, (![D_108]: (k9_relat_1('#skF_3', D_108)='#skF_2' | ~r1_tarski('#skF_2', k9_relat_1('#skF_3', D_108)))), inference(resolution, [status(thm)], [c_432, c_2])).
% 9.13/3.30  tff(c_7987, plain, (![D_108]: (k9_relat_1('#skF_3', D_108)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7980, c_439])).
% 9.13/3.30  tff(c_2679, plain, (![B_335, A_336]: (k10_relat_1(B_335, k9_relat_1(B_335, A_336))=A_336 | ~v2_funct_1(B_335) | ~r1_tarski(A_336, k1_relat_1(B_335)) | ~v1_funct_1(B_335) | ~v1_relat_1(B_335))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.13/3.30  tff(c_2689, plain, (![B_335]: (k10_relat_1(B_335, k9_relat_1(B_335, k1_xboole_0))=k1_xboole_0 | ~v2_funct_1(B_335) | ~v1_funct_1(B_335) | ~v1_relat_1(B_335))), inference(resolution, [status(thm)], [c_8, c_2679])).
% 9.13/3.30  tff(c_8153, plain, (![B_819]: (k10_relat_1(B_819, k9_relat_1(B_819, '#skF_2'))='#skF_2' | ~v2_funct_1(B_819) | ~v1_funct_1(B_819) | ~v1_relat_1(B_819))), inference(demodulation, [status(thm), theory('equality')], [c_7962, c_7962, c_2689])).
% 9.13/3.30  tff(c_8167, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7987, c_8153])).
% 9.13/3.30  tff(c_8173, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_8167])).
% 9.13/3.30  tff(c_9419, plain, (k10_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9407, c_9407, c_8173])).
% 9.13/3.30  tff(c_9429, plain, (![D_108]: (k9_relat_1('#skF_3', D_108)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9407, c_7987])).
% 9.13/3.30  tff(c_9596, plain, (![B_928]: (k10_relat_1(B_928, k9_relat_1(B_928, k1_relat_1(B_928)))=k1_relat_1(B_928) | ~v2_funct_1(B_928) | ~v1_funct_1(B_928) | ~v1_relat_1(B_928))), inference(resolution, [status(thm)], [c_6, c_2679])).
% 9.13/3.30  tff(c_9610, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9429, c_9596])).
% 9.13/3.30  tff(c_9622, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_9419, c_9610])).
% 9.13/3.30  tff(c_9624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7963, c_9622])).
% 9.13/3.30  tff(c_9625, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_9405])).
% 9.13/3.30  tff(c_9650, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_9625, c_7980])).
% 9.13/3.30  tff(c_2701, plain, (![B_338, A_339, C_340]: (k1_xboole_0=B_338 | k1_relset_1(A_339, B_338, C_340)=A_339 | ~v1_funct_2(C_340, A_339, B_338) | ~m1_subset_1(C_340, k1_zfmisc_1(k2_zfmisc_1(A_339, B_338))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.13/3.30  tff(c_2719, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_2701])).
% 9.13/3.30  tff(c_2727, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_233, c_2719])).
% 9.13/3.30  tff(c_2728, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_2727])).
% 9.13/3.30  tff(c_4195, plain, (![A_495, A_496]: (v1_funct_2(k2_funct_1(A_495), k2_relat_1(A_495), A_496) | ~r1_tarski(k2_relat_1(k2_funct_1(A_495)), A_496) | ~v1_funct_1(k2_funct_1(A_495)) | ~v1_relat_1(k2_funct_1(A_495)) | ~v2_funct_1(A_495) | ~v1_funct_1(A_495) | ~v1_relat_1(A_495))), inference(superposition, [status(thm), theory('equality')], [c_26, c_309])).
% 9.13/3.30  tff(c_4198, plain, (![A_496]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_496) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_496) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_287, c_4195])).
% 9.13/3.30  tff(c_4203, plain, (![A_496]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_496) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_496) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_132, c_4198])).
% 9.13/3.30  tff(c_4204, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_4203])).
% 9.13/3.30  tff(c_4207, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_4204])).
% 9.13/3.30  tff(c_4211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_4207])).
% 9.13/3.30  tff(c_4213, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_4203])).
% 9.13/3.30  tff(c_4274, plain, (![A_503, A_504]: (m1_subset_1(k2_funct_1(A_503), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_503), A_504))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_503)), A_504) | ~v1_funct_1(k2_funct_1(A_503)) | ~v1_relat_1(k2_funct_1(A_503)) | ~v2_funct_1(A_503) | ~v1_funct_1(A_503) | ~v1_relat_1(A_503))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2494])).
% 9.13/3.30  tff(c_4305, plain, (![A_504]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_504))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_504) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_287, c_4274])).
% 9.13/3.30  tff(c_4350, plain, (![A_507]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_507))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_507))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_4213, c_132, c_4305])).
% 9.13/3.30  tff(c_4390, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_4350, c_192])).
% 9.13/3.30  tff(c_4397, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_4390])).
% 9.13/3.30  tff(c_4400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_6, c_2728, c_4397])).
% 9.13/3.30  tff(c_4401, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2727])).
% 9.13/3.30  tff(c_5773, plain, (![A_617, A_618]: (A_617='#skF_2' | ~v1_funct_2(A_617, A_618, '#skF_2') | A_618='#skF_2' | ~r1_tarski(A_617, k2_zfmisc_1(A_618, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4401, c_4401, c_4401, c_4401, c_334])).
% 9.13/3.30  tff(c_5788, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_77, c_5773])).
% 9.13/3.30  tff(c_5799, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5788])).
% 9.13/3.30  tff(c_5801, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_5799])).
% 9.13/3.30  tff(c_238, plain, (![A_65, B_66, A_67]: (k1_relset_1(A_65, B_66, A_67)=k1_relat_1(A_67) | ~r1_tarski(A_67, k2_zfmisc_1(A_65, B_66)))), inference(resolution, [status(thm)], [c_12, c_224])).
% 9.13/3.30  tff(c_253, plain, (![A_65, B_66]: (k1_relset_1(A_65, B_66, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_238])).
% 9.13/3.30  tff(c_365, plain, (![A_96, B_97, A_98, D_99]: (k7_relset_1(A_96, B_97, A_98, D_99)=k9_relat_1(A_98, D_99) | ~r1_tarski(A_98, k2_zfmisc_1(A_96, B_97)))), inference(resolution, [status(thm)], [c_12, c_348])).
% 9.13/3.30  tff(c_377, plain, (![A_96, B_97, D_99]: (k7_relset_1(A_96, B_97, k1_xboole_0, D_99)=k9_relat_1(k1_xboole_0, D_99))), inference(resolution, [status(thm)], [c_8, c_365])).
% 9.13/3.30  tff(c_2487, plain, (![D_319, B_320, A_321]: (m1_subset_1(k9_relat_1(k1_xboole_0, D_319), k1_zfmisc_1(B_320)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_321, B_320))))), inference(superposition, [status(thm), theory('equality')], [c_377, c_387])).
% 9.13/3.30  tff(c_2490, plain, (![D_319, B_320, A_321]: (m1_subset_1(k9_relat_1(k1_xboole_0, D_319), k1_zfmisc_1(B_320)) | ~r1_tarski(k1_xboole_0, k2_zfmisc_1(A_321, B_320)))), inference(resolution, [status(thm)], [c_12, c_2487])).
% 9.13/3.30  tff(c_2531, plain, (![D_324, B_325]: (m1_subset_1(k9_relat_1(k1_xboole_0, D_324), k1_zfmisc_1(B_325)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2490])).
% 9.13/3.30  tff(c_2564, plain, (![D_326, B_327]: (r1_tarski(k9_relat_1(k1_xboole_0, D_326), B_327))), inference(resolution, [status(thm)], [c_2531, c_10])).
% 9.13/3.30  tff(c_140, plain, (![B_53, A_54]: (B_53=A_54 | ~r1_tarski(B_53, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.13/3.30  tff(c_152, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_140])).
% 9.13/3.30  tff(c_2594, plain, (![D_326]: (k9_relat_1(k1_xboole_0, D_326)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2564, c_152])).
% 9.13/3.30  tff(c_2493, plain, (![D_319, B_320]: (m1_subset_1(k9_relat_1(k1_xboole_0, D_319), k1_zfmisc_1(B_320)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2490])).
% 9.13/3.30  tff(c_2607, plain, (![B_329]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(B_329)))), inference(demodulation, [status(thm), theory('equality')], [c_2594, c_2493])).
% 9.13/3.30  tff(c_44, plain, (![B_30, C_31]: (k1_relset_1(k1_xboole_0, B_30, C_31)=k1_xboole_0 | ~v1_funct_2(C_31, k1_xboole_0, B_30) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_30))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.13/3.30  tff(c_2611, plain, (![B_30]: (k1_relset_1(k1_xboole_0, B_30, k1_xboole_0)=k1_xboole_0 | ~v1_funct_2(k1_xboole_0, k1_xboole_0, B_30))), inference(resolution, [status(thm)], [c_2607, c_44])).
% 9.13/3.30  tff(c_2634, plain, (![B_30]: (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_funct_2(k1_xboole_0, k1_xboole_0, B_30))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_2611])).
% 9.13/3.30  tff(c_2690, plain, (![B_30]: (~v1_funct_2(k1_xboole_0, k1_xboole_0, B_30))), inference(splitLeft, [status(thm)], [c_2634])).
% 9.13/3.30  tff(c_2597, plain, (![B_320]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(B_320)))), inference(demodulation, [status(thm), theory('equality')], [c_2594, c_2493])).
% 9.13/3.30  tff(c_2648, plain, (![C_330, B_331]: (v1_funct_2(C_330, k1_xboole_0, B_331) | k1_relset_1(k1_xboole_0, B_331, C_330)!=k1_xboole_0 | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_331))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.13/3.30  tff(c_2652, plain, (![B_331]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_331) | k1_relset_1(k1_xboole_0, B_331, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2597, c_2648])).
% 9.13/3.30  tff(c_2662, plain, (![B_331]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_331) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_253, c_2652])).
% 9.13/3.30  tff(c_2698, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2690, c_2662])).
% 9.13/3.30  tff(c_4404, plain, (k1_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4401, c_4401, c_2698])).
% 9.13/3.30  tff(c_5823, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5801, c_5801, c_4404])).
% 9.13/3.30  tff(c_14, plain, (![B_8, A_6]: (v1_relat_1(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.13/3.30  tff(c_430, plain, (![D_107]: (v1_relat_1(k9_relat_1('#skF_3', D_107)) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_423, c_14])).
% 9.13/3.30  tff(c_440, plain, (~v1_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_430])).
% 9.13/3.30  tff(c_679, plain, (![B_134, A_135, C_136]: (k1_xboole_0=B_134 | k1_relset_1(A_135, B_134, C_136)=A_135 | ~v1_funct_2(C_136, A_135, B_134) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_135, B_134))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.13/3.30  tff(c_697, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_679])).
% 9.13/3.30  tff(c_705, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_233, c_697])).
% 9.13/3.30  tff(c_706, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_705])).
% 9.13/3.30  tff(c_2229, plain, (![A_297, A_298]: (v1_funct_2(k2_funct_1(A_297), k2_relat_1(A_297), A_298) | ~r1_tarski(k2_relat_1(k2_funct_1(A_297)), A_298) | ~v1_funct_1(k2_funct_1(A_297)) | ~v1_relat_1(k2_funct_1(A_297)) | ~v2_funct_1(A_297) | ~v1_funct_1(A_297) | ~v1_relat_1(A_297))), inference(superposition, [status(thm), theory('equality')], [c_26, c_309])).
% 9.13/3.30  tff(c_2232, plain, (![A_298]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_298) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_298) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_287, c_2229])).
% 9.13/3.30  tff(c_2237, plain, (![A_298]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_298) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_298) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_132, c_2232])).
% 9.13/3.30  tff(c_2238, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2237])).
% 9.13/3.30  tff(c_2241, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_2238])).
% 9.13/3.30  tff(c_2245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_2241])).
% 9.13/3.30  tff(c_2247, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2237])).
% 9.13/3.30  tff(c_472, plain, (![B_118, A_119]: (m1_subset_1(B_118, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_118), A_119))) | ~r1_tarski(k2_relat_1(B_118), A_119) | ~v1_funct_1(B_118) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.13/3.30  tff(c_2328, plain, (![A_308, A_309]: (m1_subset_1(k2_funct_1(A_308), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_308), A_309))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_308)), A_309) | ~v1_funct_1(k2_funct_1(A_308)) | ~v1_relat_1(k2_funct_1(A_308)) | ~v2_funct_1(A_308) | ~v1_funct_1(A_308) | ~v1_relat_1(A_308))), inference(superposition, [status(thm), theory('equality')], [c_26, c_472])).
% 9.13/3.30  tff(c_2359, plain, (![A_309]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_309))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_309) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_287, c_2328])).
% 9.13/3.30  tff(c_2386, plain, (![A_311]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_311))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_311))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_2247, c_132, c_2359])).
% 9.13/3.30  tff(c_2426, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_2386, c_192])).
% 9.13/3.30  tff(c_2433, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_2426])).
% 9.13/3.30  tff(c_2436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_6, c_706, c_2433])).
% 9.13/3.30  tff(c_2437, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_705])).
% 9.13/3.30  tff(c_177, plain, (![A_58, B_59]: (v1_relat_1(A_58) | ~v1_relat_1(B_59) | ~r1_tarski(A_58, B_59))), inference(resolution, [status(thm)], [c_12, c_153])).
% 9.13/3.30  tff(c_191, plain, (![A_3]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_3))), inference(resolution, [status(thm)], [c_8, c_177])).
% 9.13/3.30  tff(c_193, plain, (![A_3]: (~v1_relat_1(A_3))), inference(splitLeft, [status(thm)], [c_191])).
% 9.13/3.30  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_193, c_163])).
% 9.13/3.30  tff(c_200, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_191])).
% 9.13/3.30  tff(c_2453, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_200])).
% 9.13/3.30  tff(c_2457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_440, c_2453])).
% 9.13/3.30  tff(c_2459, plain, (v1_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_430])).
% 9.13/3.30  tff(c_5826, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5801, c_2459])).
% 9.13/3.30  tff(c_4402, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_2727])).
% 9.13/3.30  tff(c_4768, plain, (![A_545, A_546]: (A_545='#skF_2' | ~v1_funct_2(A_545, A_546, '#skF_2') | A_546='#skF_2' | ~r1_tarski(A_545, k2_zfmisc_1(A_546, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4401, c_4401, c_4401, c_4401, c_334])).
% 9.13/3.30  tff(c_4783, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_77, c_4768])).
% 9.13/3.30  tff(c_4794, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4783])).
% 9.13/3.30  tff(c_4796, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_4794])).
% 9.13/3.30  tff(c_4419, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4401, c_8])).
% 9.13/3.30  tff(c_4426, plain, (![D_108]: (k9_relat_1('#skF_3', D_108)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4419, c_439])).
% 9.13/3.30  tff(c_4580, plain, (![B_521]: (k10_relat_1(B_521, k9_relat_1(B_521, '#skF_2'))='#skF_2' | ~v2_funct_1(B_521) | ~v1_funct_1(B_521) | ~v1_relat_1(B_521))), inference(demodulation, [status(thm), theory('equality')], [c_4401, c_4401, c_2689])).
% 9.13/3.30  tff(c_4594, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4426, c_4580])).
% 9.13/3.30  tff(c_4600, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_4594])).
% 9.13/3.30  tff(c_4803, plain, (k10_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4796, c_4796, c_4600])).
% 9.13/3.30  tff(c_4813, plain, (![D_108]: (k9_relat_1('#skF_3', D_108)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4796, c_4426])).
% 9.13/3.30  tff(c_4991, plain, (![B_555]: (k10_relat_1(B_555, k9_relat_1(B_555, k1_relat_1(B_555)))=k1_relat_1(B_555) | ~v2_funct_1(B_555) | ~v1_funct_1(B_555) | ~v1_relat_1(B_555))), inference(resolution, [status(thm)], [c_6, c_2679])).
% 9.13/3.30  tff(c_5005, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4813, c_4991])).
% 9.13/3.30  tff(c_5014, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_4803, c_5005])).
% 9.13/3.30  tff(c_5016, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4402, c_5014])).
% 9.13/3.30  tff(c_5017, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_4794])).
% 9.13/3.30  tff(c_4409, plain, (![D_326]: (k9_relat_1('#skF_2', D_326)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4401, c_4401, c_2594])).
% 9.13/3.30  tff(c_4590, plain, (k10_relat_1('#skF_2', '#skF_2')='#skF_2' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4409, c_4580])).
% 9.13/3.30  tff(c_4598, plain, (k10_relat_1('#skF_2', '#skF_2')='#skF_2' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2459, c_4590])).
% 9.13/3.30  tff(c_4629, plain, (~v1_funct_1('#skF_2')), inference(splitLeft, [status(thm)], [c_4598])).
% 9.13/3.30  tff(c_5022, plain, (~v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5017, c_4629])).
% 9.13/3.30  tff(c_5051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_5022])).
% 9.13/3.30  tff(c_5053, plain, (v1_funct_1('#skF_2')), inference(splitRight, [status(thm)], [c_4598])).
% 9.13/3.30  tff(c_5809, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5801, c_5053])).
% 9.13/3.30  tff(c_5256, plain, (![A_582, A_583]: (A_582='#skF_2' | ~v1_funct_2(A_582, A_583, '#skF_2') | A_583='#skF_2' | ~r1_tarski(A_582, k2_zfmisc_1(A_583, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4401, c_4401, c_4401, c_4401, c_334])).
% 9.13/3.30  tff(c_5271, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_77, c_5256])).
% 9.13/3.30  tff(c_5282, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5271])).
% 9.13/3.30  tff(c_5284, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_5282])).
% 9.13/3.30  tff(c_5296, plain, (k10_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5284, c_5284, c_4600])).
% 9.13/3.30  tff(c_5371, plain, (![D_586]: (k9_relat_1('#skF_3', D_586)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5284, c_4426])).
% 9.13/3.30  tff(c_2688, plain, (![B_335]: (k10_relat_1(B_335, k9_relat_1(B_335, k1_relat_1(B_335)))=k1_relat_1(B_335) | ~v2_funct_1(B_335) | ~v1_funct_1(B_335) | ~v1_relat_1(B_335))), inference(resolution, [status(thm)], [c_6, c_2679])).
% 9.13/3.30  tff(c_5377, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5371, c_2688])).
% 9.13/3.30  tff(c_5382, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_5377])).
% 9.13/3.30  tff(c_5539, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5296, c_5382])).
% 9.13/3.30  tff(c_5540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4402, c_5539])).
% 9.13/3.30  tff(c_5541, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_5282])).
% 9.13/3.30  tff(c_5052, plain, (~v2_funct_1('#skF_2') | k10_relat_1('#skF_2', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_4598])).
% 9.13/3.30  tff(c_5054, plain, (~v2_funct_1('#skF_2')), inference(splitLeft, [status(thm)], [c_5052])).
% 9.13/3.30  tff(c_5550, plain, (~v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5541, c_5054])).
% 9.13/3.30  tff(c_5580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_5550])).
% 9.13/3.30  tff(c_5582, plain, (v2_funct_1('#skF_2')), inference(splitRight, [status(thm)], [c_5052])).
% 9.13/3.30  tff(c_5808, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5801, c_5582])).
% 9.13/3.30  tff(c_5581, plain, (k10_relat_1('#skF_2', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_5052])).
% 9.13/3.30  tff(c_5807, plain, (k10_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5801, c_5801, c_5801, c_5581])).
% 9.13/3.30  tff(c_5820, plain, (![D_326]: (k9_relat_1('#skF_1', D_326)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5801, c_5801, c_4409])).
% 9.13/3.30  tff(c_5982, plain, (![B_626]: (k10_relat_1(B_626, k9_relat_1(B_626, k1_relat_1(B_626)))=k1_relat_1(B_626) | ~v2_funct_1(B_626) | ~v1_funct_1(B_626) | ~v1_relat_1(B_626))), inference(resolution, [status(thm)], [c_6, c_2679])).
% 9.13/3.30  tff(c_5992, plain, (k10_relat_1('#skF_1', '#skF_1')=k1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5820, c_5982])).
% 9.13/3.30  tff(c_6003, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5826, c_5809, c_5808, c_5807, c_5992])).
% 9.13/3.30  tff(c_6005, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5823, c_6003])).
% 9.13/3.30  tff(c_6006, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_5799])).
% 9.13/3.30  tff(c_6029, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6006, c_6006, c_4404])).
% 9.13/3.30  tff(c_6018, plain, (k10_relat_1('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6006, c_6006, c_4600])).
% 9.13/3.30  tff(c_6028, plain, (![D_108]: (k9_relat_1('#skF_3', D_108)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6006, c_4426])).
% 9.13/3.30  tff(c_6190, plain, (![B_636]: (k10_relat_1(B_636, k9_relat_1(B_636, k1_relat_1(B_636)))=k1_relat_1(B_636) | ~v2_funct_1(B_636) | ~v1_funct_1(B_636) | ~v1_relat_1(B_636))), inference(resolution, [status(thm)], [c_6, c_2679])).
% 9.13/3.30  tff(c_6200, plain, (k10_relat_1('#skF_3', '#skF_3')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6028, c_6190])).
% 9.13/3.30  tff(c_6207, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_6018, c_6200])).
% 9.13/3.30  tff(c_6209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6029, c_6207])).
% 9.13/3.30  tff(c_6210, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_2634])).
% 9.13/3.30  tff(c_7967, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7962, c_7962, c_6210])).
% 9.13/3.30  tff(c_9649, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9625, c_9625, c_7967])).
% 9.13/3.30  tff(c_9653, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9625, c_287])).
% 9.13/3.30  tff(c_10967, plain, (![A_1063, A_1064]: (v1_funct_2(k2_funct_1(A_1063), k2_relat_1(A_1063), A_1064) | ~r1_tarski(k2_relat_1(k2_funct_1(A_1063)), A_1064) | ~v1_funct_1(k2_funct_1(A_1063)) | ~v1_relat_1(k2_funct_1(A_1063)) | ~v2_funct_1(A_1063) | ~v1_funct_1(A_1063) | ~v1_relat_1(A_1063))), inference(superposition, [status(thm), theory('equality')], [c_26, c_309])).
% 9.13/3.30  tff(c_10970, plain, (![A_1064]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', A_1064) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_1064) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_9653, c_10967])).
% 9.13/3.30  tff(c_10975, plain, (![A_1064]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', A_1064) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_1064) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_132, c_10970])).
% 9.13/3.30  tff(c_10976, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_10975])).
% 9.13/3.30  tff(c_10979, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_10976])).
% 9.13/3.30  tff(c_10983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_10979])).
% 9.13/3.30  tff(c_10985, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_10975])).
% 9.13/3.30  tff(c_11061, plain, (![A_1071, A_1072]: (m1_subset_1(k2_funct_1(A_1071), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1071), A_1072))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_1071)), A_1072) | ~v1_funct_1(k2_funct_1(A_1071)) | ~v1_relat_1(k2_funct_1(A_1071)) | ~v2_funct_1(A_1071) | ~v1_funct_1(A_1071) | ~v1_relat_1(A_1071))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2494])).
% 9.13/3.30  tff(c_11092, plain, (![A_1072]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_1072))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_1072) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_9653, c_11061])).
% 9.13/3.30  tff(c_11110, plain, (![A_1073]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_1073))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_1073))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_10985, c_132, c_11092])).
% 9.13/3.30  tff(c_9657, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_9625, c_192])).
% 9.13/3.30  tff(c_11162, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_11110, c_9657])).
% 9.13/3.30  tff(c_11174, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_11162])).
% 9.13/3.30  tff(c_11177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_9650, c_9649, c_11174])).
% 9.13/3.30  tff(c_11178, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_131])).
% 9.13/3.30  tff(c_11179, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_131])).
% 9.13/3.30  tff(c_11250, plain, (![A_1079, B_1080, C_1081]: (k1_relset_1(A_1079, B_1080, C_1081)=k1_relat_1(C_1081) | ~m1_subset_1(C_1081, k1_zfmisc_1(k2_zfmisc_1(A_1079, B_1080))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.13/3.30  tff(c_11261, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_11179, c_11250])).
% 9.13/3.30  tff(c_13222, plain, (![B_1285, C_1286, A_1287]: (k1_xboole_0=B_1285 | v1_funct_2(C_1286, A_1287, B_1285) | k1_relset_1(A_1287, B_1285, C_1286)!=A_1287 | ~m1_subset_1(C_1286, k1_zfmisc_1(k2_zfmisc_1(A_1287, B_1285))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.13/3.30  tff(c_13236, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_11179, c_13222])).
% 9.13/3.30  tff(c_13249, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11261, c_13236])).
% 9.13/3.30  tff(c_13250, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_11178, c_13249])).
% 9.13/3.30  tff(c_13255, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_13250])).
% 9.13/3.30  tff(c_13258, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_13255])).
% 9.13/3.30  tff(c_13261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_11241, c_13258])).
% 9.13/3.30  tff(c_13262, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_13250])).
% 9.13/3.30  tff(c_13281, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_13262, c_8])).
% 9.13/3.30  tff(c_11263, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_11250])).
% 9.13/3.30  tff(c_13164, plain, (![B_1281, A_1282, C_1283]: (k1_xboole_0=B_1281 | k1_relset_1(A_1282, B_1281, C_1283)=A_1282 | ~v1_funct_2(C_1283, A_1282, B_1281) | ~m1_subset_1(C_1283, k1_zfmisc_1(k2_zfmisc_1(A_1282, B_1281))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.13/3.30  tff(c_13185, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_13164])).
% 9.13/3.30  tff(c_13195, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_11263, c_13185])).
% 9.13/3.30  tff(c_13196, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_13195])).
% 9.13/3.30  tff(c_11190, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_11179, c_14])).
% 9.13/3.30  tff(c_11196, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_11190])).
% 9.13/3.30  tff(c_13263, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_13250])).
% 9.13/3.30  tff(c_50, plain, (![B_33, A_32]: (v1_funct_2(B_33, k1_relat_1(B_33), A_32) | ~r1_tarski(k2_relat_1(B_33), A_32) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.13/3.30  tff(c_13296, plain, (![A_32]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_32) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_32) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_13263, c_50])).
% 9.13/3.30  tff(c_13650, plain, (![A_1319]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_1319) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_1319))), inference(demodulation, [status(thm), theory('equality')], [c_11196, c_132, c_13296])).
% 9.13/3.30  tff(c_13653, plain, (![A_1319]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_1319) | ~r1_tarski(k1_relat_1('#skF_3'), A_1319) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_13650])).
% 9.13/3.30  tff(c_13659, plain, (![A_1319]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_1319))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_13281, c_13196, c_13653])).
% 9.13/3.30  tff(c_13705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13659, c_11178])).
% 9.13/3.30  tff(c_13707, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_13195])).
% 9.13/3.30  tff(c_13706, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_13195])).
% 9.13/3.30  tff(c_42, plain, (![B_30, C_31, A_29]: (k1_xboole_0=B_30 | v1_funct_2(C_31, A_29, B_30) | k1_relset_1(A_29, B_30, C_31)!=A_29 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.13/3.30  tff(c_13772, plain, (![B_1324, C_1325, A_1326]: (B_1324='#skF_2' | v1_funct_2(C_1325, A_1326, B_1324) | k1_relset_1(A_1326, B_1324, C_1325)!=A_1326 | ~m1_subset_1(C_1325, k1_zfmisc_1(k2_zfmisc_1(A_1326, B_1324))))), inference(demodulation, [status(thm), theory('equality')], [c_13706, c_42])).
% 9.13/3.30  tff(c_13782, plain, ('#skF_2'='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_11179, c_13772])).
% 9.13/3.30  tff(c_13793, plain, ('#skF_2'='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11261, c_13782])).
% 9.13/3.30  tff(c_13794, plain, ('#skF_2'='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_11178, c_13793])).
% 9.13/3.30  tff(c_13921, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_13794])).
% 9.13/3.30  tff(c_13924, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_13921])).
% 9.13/3.30  tff(c_13927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_64, c_58, c_11241, c_13924])).
% 9.13/3.30  tff(c_13928, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_13794])).
% 9.13/3.30  tff(c_13958, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13928, c_62])).
% 9.13/3.30  tff(c_13947, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13928, c_11263])).
% 9.13/3.30  tff(c_13955, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_13928, c_77])).
% 9.13/3.30  tff(c_13943, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13928, c_13706])).
% 9.13/3.30  tff(c_13057, plain, (![B_1271, C_1272]: (k1_relset_1(k1_xboole_0, B_1271, C_1272)=k1_xboole_0 | ~v1_funct_2(C_1272, k1_xboole_0, B_1271) | ~m1_subset_1(C_1272, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_1271))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.13/3.30  tff(c_13072, plain, (![B_1271, A_4]: (k1_relset_1(k1_xboole_0, B_1271, A_4)=k1_xboole_0 | ~v1_funct_2(A_4, k1_xboole_0, B_1271) | ~r1_tarski(A_4, k2_zfmisc_1(k1_xboole_0, B_1271)))), inference(resolution, [status(thm)], [c_12, c_13057])).
% 9.13/3.30  tff(c_14277, plain, (![B_1361, A_1362]: (k1_relset_1('#skF_1', B_1361, A_1362)='#skF_1' | ~v1_funct_2(A_1362, '#skF_1', B_1361) | ~r1_tarski(A_1362, k2_zfmisc_1('#skF_1', B_1361)))), inference(demodulation, [status(thm), theory('equality')], [c_13943, c_13943, c_13943, c_13943, c_13072])).
% 9.13/3.30  tff(c_14283, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_13955, c_14277])).
% 9.13/3.30  tff(c_14296, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13958, c_13947, c_14283])).
% 9.13/3.30  tff(c_14298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13707, c_14296])).
% 9.13/3.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.13/3.30  
% 9.13/3.30  Inference rules
% 9.13/3.30  ----------------------
% 9.13/3.30  #Ref     : 0
% 9.13/3.30  #Sup     : 2882
% 9.13/3.30  #Fact    : 0
% 9.13/3.30  #Define  : 0
% 9.13/3.30  #Split   : 55
% 9.13/3.30  #Chain   : 0
% 9.13/3.30  #Close   : 0
% 9.13/3.30  
% 9.13/3.30  Ordering : KBO
% 9.13/3.30  
% 9.13/3.30  Simplification rules
% 9.13/3.30  ----------------------
% 9.13/3.30  #Subsume      : 384
% 9.13/3.30  #Demod        : 3607
% 9.13/3.30  #Tautology    : 1323
% 9.13/3.30  #SimpNegUnit  : 45
% 9.13/3.30  #BackRed      : 638
% 9.13/3.30  
% 9.13/3.30  #Partial instantiations: 0
% 9.13/3.30  #Strategies tried      : 1
% 9.13/3.30  
% 9.13/3.30  Timing (in seconds)
% 9.13/3.30  ----------------------
% 9.13/3.31  Preprocessing        : 0.34
% 9.13/3.31  Parsing              : 0.19
% 9.13/3.31  CNF conversion       : 0.02
% 9.13/3.31  Main loop            : 2.07
% 9.13/3.31  Inferencing          : 0.70
% 9.13/3.31  Reduction            : 0.71
% 9.13/3.31  Demodulation         : 0.51
% 9.13/3.31  BG Simplification    : 0.09
% 9.13/3.31  Subsumption          : 0.38
% 9.13/3.31  Abstraction          : 0.10
% 9.13/3.31  MUC search           : 0.00
% 9.13/3.31  Cooper               : 0.00
% 9.13/3.31  Total                : 2.51
% 9.13/3.31  Index Insertion      : 0.00
% 9.13/3.31  Index Deletion       : 0.00
% 9.13/3.31  Index Matching       : 0.00
% 9.13/3.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
