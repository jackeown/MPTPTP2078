%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:39 EST 2020

% Result     : Theorem 10.41s
% Output     : CNFRefutation 10.85s
% Verified   : 
% Statistics : Number of formulae       :  313 (10421 expanded)
%              Number of leaves         :   41 (3550 expanded)
%              Depth                    :   26
%              Number of atoms          :  657 (30984 expanded)
%              Number of equality atoms :  172 (9173 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_117,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_16555,plain,(
    ! [C_1030,A_1031,B_1032] :
      ( v1_relat_1(C_1030)
      | ~ m1_subset_1(C_1030,k1_zfmisc_1(k2_zfmisc_1(A_1031,B_1032))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16568,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_16555])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_64,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_17091,plain,(
    ! [A_1109,B_1110,C_1111] :
      ( k2_relset_1(A_1109,B_1110,C_1111) = k2_relat_1(C_1111)
      | ~ m1_subset_1(C_1111,k1_zfmisc_1(k2_zfmisc_1(A_1109,B_1110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_17101,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_17091])).

tff(c_17105,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_17101])).

tff(c_30,plain,(
    ! [A_15] :
      ( k1_relat_1(k2_funct_1(A_15)) = k2_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_153,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_162,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_153])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_12] :
      ( v1_relat_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_568,plain,(
    ! [A_118,B_119,C_120] :
      ( k1_relset_1(A_118,B_119,C_120) = k1_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_577,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_568])).

tff(c_9313,plain,(
    ! [B_654,A_655,C_656] :
      ( k1_xboole_0 = B_654
      | k1_relset_1(A_655,B_654,C_656) = A_655
      | ~ v1_funct_2(C_656,A_655,B_654)
      | ~ m1_subset_1(C_656,k1_zfmisc_1(k2_zfmisc_1(A_655,B_654))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_9326,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_9313])).

tff(c_9334,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_577,c_9326])).

tff(c_9335,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9334])).

tff(c_402,plain,(
    ! [A_91] :
      ( k2_relat_1(k2_funct_1(A_91)) = k1_relat_1(A_91)
      | ~ v2_funct_1(A_91)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_206,plain,(
    ! [B_61,A_62] :
      ( v5_relat_1(B_61,A_62)
      | ~ r1_tarski(k2_relat_1(B_61),A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_211,plain,(
    ! [B_61] :
      ( v5_relat_1(B_61,k2_relat_1(B_61))
      | ~ v1_relat_1(B_61) ) ),
    inference(resolution,[status(thm)],[c_6,c_206])).

tff(c_9778,plain,(
    ! [A_676] :
      ( v5_relat_1(k2_funct_1(A_676),k1_relat_1(A_676))
      | ~ v1_relat_1(k2_funct_1(A_676))
      | ~ v2_funct_1(A_676)
      | ~ v1_funct_1(A_676)
      | ~ v1_relat_1(A_676) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_211])).

tff(c_9781,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9335,c_9778])).

tff(c_9789,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_70,c_64,c_9781])).

tff(c_9792,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_9789])).

tff(c_9795,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_9792])).

tff(c_9799,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_70,c_9795])).

tff(c_9801,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_9789])).

tff(c_81,plain,(
    ! [A_38] :
      ( v1_funct_1(k2_funct_1(A_38))
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_60,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_80,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_84,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_81,c_80])).

tff(c_87,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_84])).

tff(c_123,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_130,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_123])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_130])).

tff(c_137,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_9800,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_9789])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10938,plain,(
    ! [A_760,A_761] :
      ( r1_tarski(k1_relat_1(A_760),A_761)
      | ~ v5_relat_1(k2_funct_1(A_760),A_761)
      | ~ v1_relat_1(k2_funct_1(A_760))
      | ~ v2_funct_1(A_760)
      | ~ v1_funct_1(A_760)
      | ~ v1_relat_1(A_760) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_16])).

tff(c_10961,plain,(
    ! [A_762] :
      ( r1_tarski(k1_relat_1(A_762),k2_relat_1(k2_funct_1(A_762)))
      | ~ v2_funct_1(A_762)
      | ~ v1_funct_1(A_762)
      | ~ v1_relat_1(A_762)
      | ~ v1_relat_1(k2_funct_1(A_762)) ) ),
    inference(resolution,[status(thm)],[c_211,c_10938])).

tff(c_10972,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9335,c_10961])).

tff(c_10987,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9801,c_162,c_70,c_64,c_10972])).

tff(c_310,plain,(
    ! [B_84,A_85] :
      ( r1_tarski(k2_relat_1(B_84),A_85)
      | ~ v5_relat_1(B_84,A_85)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_339,plain,(
    ! [B_84,A_85] :
      ( k2_relat_1(B_84) = A_85
      | ~ r1_tarski(A_85,k2_relat_1(B_84))
      | ~ v5_relat_1(B_84,A_85)
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_310,c_2])).

tff(c_10993,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_10987,c_339])).

tff(c_11001,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9801,c_9800,c_10993])).

tff(c_661,plain,(
    ! [A_133,B_134,C_135] :
      ( k2_relset_1(A_133,B_134,C_135) = k2_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_668,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_661])).

tff(c_671,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_668])).

tff(c_1038,plain,(
    ! [B_183,A_184] :
      ( m1_subset_1(B_183,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_183),A_184)))
      | ~ r1_tarski(k2_relat_1(B_183),A_184)
      | ~ v1_funct_1(B_183)
      | ~ v1_relat_1(B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_12112,plain,(
    ! [A_788,A_789] :
      ( m1_subset_1(k2_funct_1(A_788),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_788),A_789)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_788)),A_789)
      | ~ v1_funct_1(k2_funct_1(A_788))
      | ~ v1_relat_1(k2_funct_1(A_788))
      | ~ v2_funct_1(A_788)
      | ~ v1_funct_1(A_788)
      | ~ v1_relat_1(A_788) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1038])).

tff(c_12155,plain,(
    ! [A_789] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_789)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_789)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_12112])).

tff(c_12196,plain,(
    ! [A_790] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_790)))
      | ~ r1_tarski('#skF_1',A_790) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_70,c_64,c_9801,c_137,c_11001,c_12155])).

tff(c_136,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_138,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_12224,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_12196,c_138])).

tff(c_12241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12224])).

tff(c_12243,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9334])).

tff(c_140,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_148,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_140])).

tff(c_12242,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_9334])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_855,plain,(
    ! [C_162,A_163] :
      ( k1_xboole_0 = C_162
      | ~ v1_funct_2(C_162,A_163,k1_xboole_0)
      | k1_xboole_0 = A_163
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_163,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_860,plain,(
    ! [A_4,A_163] :
      ( k1_xboole_0 = A_4
      | ~ v1_funct_2(A_4,A_163,k1_xboole_0)
      | k1_xboole_0 = A_163
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_163,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_12,c_855])).

tff(c_12665,plain,(
    ! [A_809,A_810] :
      ( A_809 = '#skF_2'
      | ~ v1_funct_2(A_809,A_810,'#skF_2')
      | A_810 = '#skF_2'
      | ~ r1_tarski(A_809,k2_zfmisc_1(A_810,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12242,c_12242,c_12242,c_12242,c_860])).

tff(c_12676,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_148,c_12665])).

tff(c_12686,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_12676])).

tff(c_12688,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_12686])).

tff(c_12722,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12688,c_68])).

tff(c_12719,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12688,c_148])).

tff(c_995,plain,(
    ! [B_176,C_177] :
      ( k1_relset_1(k1_xboole_0,B_176,C_177) = k1_xboole_0
      | ~ v1_funct_2(C_177,k1_xboole_0,B_176)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1000,plain,(
    ! [B_176,A_4] :
      ( k1_relset_1(k1_xboole_0,B_176,A_4) = k1_xboole_0
      | ~ v1_funct_2(A_4,k1_xboole_0,B_176)
      | ~ r1_tarski(A_4,k2_zfmisc_1(k1_xboole_0,B_176)) ) ),
    inference(resolution,[status(thm)],[c_12,c_995])).

tff(c_12245,plain,(
    ! [B_176,A_4] :
      ( k1_relset_1('#skF_2',B_176,A_4) = '#skF_2'
      | ~ v1_funct_2(A_4,'#skF_2',B_176)
      | ~ r1_tarski(A_4,k2_zfmisc_1('#skF_2',B_176)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12242,c_12242,c_12242,c_12242,c_1000])).

tff(c_13055,plain,(
    ! [B_176,A_4] :
      ( k1_relset_1('#skF_1',B_176,A_4) = '#skF_1'
      | ~ v1_funct_2(A_4,'#skF_1',B_176)
      | ~ r1_tarski(A_4,k2_zfmisc_1('#skF_1',B_176)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12688,c_12688,c_12688,c_12688,c_12245])).

tff(c_13078,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_12719,c_13055])).

tff(c_13101,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12722,c_13078])).

tff(c_12715,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12688,c_577])).

tff(c_13195,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13101,c_12715])).

tff(c_13196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12243,c_13195])).

tff(c_13197,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12686])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12277,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12242,c_8])).

tff(c_13216,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13197,c_12277])).

tff(c_13224,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13197,c_671])).

tff(c_163,plain,(
    ! [A_53,A_54,B_55] :
      ( v1_relat_1(A_53)
      | ~ r1_tarski(A_53,k2_zfmisc_1(A_54,B_55)) ) ),
    inference(resolution,[status(thm)],[c_12,c_153])).

tff(c_177,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_163])).

tff(c_1237,plain,(
    ! [B_195,A_196,C_197] :
      ( k1_xboole_0 = B_195
      | k1_relset_1(A_196,B_195,C_197) = A_196
      | ~ v1_funct_2(C_197,A_196,B_195)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_196,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1247,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1237])).

tff(c_1252,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_577,c_1247])).

tff(c_1253,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1252])).

tff(c_1722,plain,(
    ! [A_228] :
      ( v5_relat_1(k2_funct_1(A_228),k1_relat_1(A_228))
      | ~ v1_relat_1(k2_funct_1(A_228))
      | ~ v2_funct_1(A_228)
      | ~ v1_funct_1(A_228)
      | ~ v1_relat_1(A_228) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_211])).

tff(c_1725,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1253,c_1722])).

tff(c_1730,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_70,c_64,c_1725])).

tff(c_1731,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1730])).

tff(c_1734,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_1731])).

tff(c_1738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_70,c_1734])).

tff(c_1740,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1730])).

tff(c_1739,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_1730])).

tff(c_2939,plain,(
    ! [A_324,A_325] :
      ( r1_tarski(k1_relat_1(A_324),A_325)
      | ~ v5_relat_1(k2_funct_1(A_324),A_325)
      | ~ v1_relat_1(k2_funct_1(A_324))
      | ~ v2_funct_1(A_324)
      | ~ v1_funct_1(A_324)
      | ~ v1_relat_1(A_324) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_16])).

tff(c_2962,plain,(
    ! [A_327] :
      ( r1_tarski(k1_relat_1(A_327),k2_relat_1(k2_funct_1(A_327)))
      | ~ v2_funct_1(A_327)
      | ~ v1_funct_1(A_327)
      | ~ v1_relat_1(A_327)
      | ~ v1_relat_1(k2_funct_1(A_327)) ) ),
    inference(resolution,[status(thm)],[c_211,c_2939])).

tff(c_2970,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1253,c_2962])).

tff(c_2980,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1740,c_162,c_70,c_64,c_2970])).

tff(c_2984,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2980,c_339])).

tff(c_2992,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1740,c_1739,c_2984])).

tff(c_4094,plain,(
    ! [A_371,A_372] :
      ( m1_subset_1(k2_funct_1(A_371),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_371),A_372)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_371)),A_372)
      | ~ v1_funct_1(k2_funct_1(A_371))
      | ~ v1_relat_1(k2_funct_1(A_371))
      | ~ v2_funct_1(A_371)
      | ~ v1_funct_1(A_371)
      | ~ v1_relat_1(A_371) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1038])).

tff(c_4134,plain,(
    ! [A_372] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_372)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_372)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_4094])).

tff(c_4173,plain,(
    ! [A_373] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_373)))
      | ~ r1_tarski('#skF_1',A_373) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_70,c_64,c_1740,c_137,c_2992,c_4134])).

tff(c_4201,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_4173,c_138])).

tff(c_4218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4201])).

tff(c_4220,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1252])).

tff(c_4219,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1252])).

tff(c_4739,plain,(
    ! [A_408,A_409] :
      ( A_408 = '#skF_2'
      | ~ v1_funct_2(A_408,A_409,'#skF_2')
      | A_409 = '#skF_2'
      | ~ r1_tarski(A_408,k2_zfmisc_1(A_409,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4219,c_4219,c_4219,c_4219,c_860])).

tff(c_4750,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_148,c_4739])).

tff(c_4760,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4750])).

tff(c_4762,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4760])).

tff(c_4797,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4762,c_68])).

tff(c_4794,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4762,c_148])).

tff(c_4786,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4762,c_4219])).

tff(c_5000,plain,(
    ! [B_176,A_4] :
      ( k1_relset_1('#skF_1',B_176,A_4) = '#skF_1'
      | ~ v1_funct_2(A_4,'#skF_1',B_176)
      | ~ r1_tarski(A_4,k2_zfmisc_1('#skF_1',B_176)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4786,c_4786,c_4786,c_4786,c_1000])).

tff(c_5076,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_4794,c_5000])).

tff(c_5096,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4797,c_5076])).

tff(c_4790,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4762,c_577])).

tff(c_5182,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5096,c_4790])).

tff(c_5183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4220,c_5182])).

tff(c_5184,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4760])).

tff(c_214,plain,(
    ! [C_66,B_67,A_68] :
      ( v5_relat_1(C_66,B_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_68,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_224,plain,(
    ! [A_69,B_70,A_71] :
      ( v5_relat_1(A_69,B_70)
      | ~ r1_tarski(A_69,k2_zfmisc_1(A_71,B_70)) ) ),
    inference(resolution,[status(thm)],[c_12,c_214])).

tff(c_238,plain,(
    ! [B_70] : v5_relat_1(k1_xboole_0,B_70) ),
    inference(resolution,[status(thm)],[c_8,c_224])).

tff(c_179,plain,(
    ! [B_56,A_57] :
      ( B_56 = A_57
      | ~ r1_tarski(B_56,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_187,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_179])).

tff(c_367,plain,(
    ! [B_90] :
      ( k2_relat_1(B_90) = k1_xboole_0
      | ~ v5_relat_1(B_90,k1_xboole_0)
      | ~ v1_relat_1(B_90) ) ),
    inference(resolution,[status(thm)],[c_310,c_187])).

tff(c_375,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_238,c_367])).

tff(c_381,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_375])).

tff(c_243,plain,(
    ! [C_75,A_76,B_77] :
      ( v4_relat_1(C_75,A_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_287,plain,(
    ! [A_80,A_81,B_82] :
      ( v4_relat_1(A_80,A_81)
      | ~ r1_tarski(A_80,k2_zfmisc_1(A_81,B_82)) ) ),
    inference(resolution,[status(thm)],[c_12,c_243])).

tff(c_303,plain,(
    ! [A_83] : v4_relat_1(k1_xboole_0,A_83) ),
    inference(resolution,[status(thm)],[c_8,c_287])).

tff(c_20,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,A_10) = B_11
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_306,plain,(
    ! [A_83] :
      ( k7_relat_1(k1_xboole_0,A_83) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_303,c_20])).

tff(c_341,plain,(
    ! [A_86] : k7_relat_1(k1_xboole_0,A_86) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_306])).

tff(c_18,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_346,plain,(
    ! [A_86] :
      ( k9_relat_1(k1_xboole_0,A_86) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_18])).

tff(c_351,plain,(
    ! [A_86] : k9_relat_1(k1_xboole_0,A_86) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_346])).

tff(c_382,plain,(
    ! [A_86] : k9_relat_1(k1_xboole_0,A_86) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_351])).

tff(c_1148,plain,(
    ! [B_190,A_191] :
      ( k10_relat_1(B_190,k9_relat_1(B_190,A_191)) = A_191
      | ~ v2_funct_1(B_190)
      | ~ r1_tarski(A_191,k1_relat_1(B_190))
      | ~ v1_funct_1(B_190)
      | ~ v1_relat_1(B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1215,plain,(
    ! [B_194] :
      ( k10_relat_1(B_194,k9_relat_1(B_194,k1_xboole_0)) = k1_xboole_0
      | ~ v2_funct_1(B_194)
      | ~ v1_funct_1(B_194)
      | ~ v1_relat_1(B_194) ) ),
    inference(resolution,[status(thm)],[c_8,c_1148])).

tff(c_1229,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_1215])).

tff(c_1235,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_1229])).

tff(c_1236,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1235])).

tff(c_4221,plain,(
    ~ v1_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4219,c_1236])).

tff(c_5207,plain,(
    ~ v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5184,c_4221])).

tff(c_5224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5207])).

tff(c_5226,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1235])).

tff(c_5382,plain,(
    ! [B_439,A_440,C_441] :
      ( k1_xboole_0 = B_439
      | k1_relset_1(A_440,B_439,C_441) = A_440
      | ~ v1_funct_2(C_441,A_440,B_439)
      | ~ m1_subset_1(C_441,k1_zfmisc_1(k2_zfmisc_1(A_440,B_439))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_5392,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_5382])).

tff(c_5397,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_577,c_5392])).

tff(c_5398,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5397])).

tff(c_5637,plain,(
    ! [A_452] :
      ( v5_relat_1(k2_funct_1(A_452),k1_relat_1(A_452))
      | ~ v1_relat_1(k2_funct_1(A_452))
      | ~ v2_funct_1(A_452)
      | ~ v1_funct_1(A_452)
      | ~ v1_relat_1(A_452) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_211])).

tff(c_5640,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5398,c_5637])).

tff(c_5645,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_70,c_64,c_5640])).

tff(c_5682,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5645])).

tff(c_5685,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_5682])).

tff(c_5689,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_70,c_5685])).

tff(c_5691,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5645])).

tff(c_5690,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_5645])).

tff(c_6868,plain,(
    ! [A_541,A_542] :
      ( r1_tarski(k1_relat_1(A_541),A_542)
      | ~ v5_relat_1(k2_funct_1(A_541),A_542)
      | ~ v1_relat_1(k2_funct_1(A_541))
      | ~ v2_funct_1(A_541)
      | ~ v1_funct_1(A_541)
      | ~ v1_relat_1(A_541) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_16])).

tff(c_7011,plain,(
    ! [A_555] :
      ( r1_tarski(k1_relat_1(A_555),k2_relat_1(k2_funct_1(A_555)))
      | ~ v2_funct_1(A_555)
      | ~ v1_funct_1(A_555)
      | ~ v1_relat_1(A_555)
      | ~ v1_relat_1(k2_funct_1(A_555)) ) ),
    inference(resolution,[status(thm)],[c_211,c_6868])).

tff(c_7019,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5398,c_7011])).

tff(c_7029,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5691,c_162,c_70,c_64,c_7019])).

tff(c_7033,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7029,c_339])).

tff(c_7041,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5691,c_5690,c_7033])).

tff(c_8103,plain,(
    ! [A_599,A_600] :
      ( m1_subset_1(k2_funct_1(A_599),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_599),A_600)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_599)),A_600)
      | ~ v1_funct_1(k2_funct_1(A_599))
      | ~ v1_relat_1(k2_funct_1(A_599))
      | ~ v2_funct_1(A_599)
      | ~ v1_funct_1(A_599)
      | ~ v1_relat_1(A_599) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1038])).

tff(c_8143,plain,(
    ! [A_600] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_600)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_600)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_8103])).

tff(c_8182,plain,(
    ! [A_601] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_601)))
      | ~ r1_tarski('#skF_1',A_601) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_70,c_64,c_5691,c_137,c_7041,c_8143])).

tff(c_8210,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_8182,c_138])).

tff(c_8227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8210])).

tff(c_8229,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5397])).

tff(c_8228,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5397])).

tff(c_8639,plain,(
    ! [A_622,A_623] :
      ( A_622 = '#skF_2'
      | ~ v1_funct_2(A_622,A_623,'#skF_2')
      | A_623 = '#skF_2'
      | ~ r1_tarski(A_622,k2_zfmisc_1(A_623,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8228,c_8228,c_8228,c_8228,c_860])).

tff(c_8654,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_148,c_8639])).

tff(c_8665,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_8654])).

tff(c_8667,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_8665])).

tff(c_8700,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8667,c_68])).

tff(c_8697,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8667,c_148])).

tff(c_8233,plain,(
    ! [B_176,A_4] :
      ( k1_relset_1('#skF_2',B_176,A_4) = '#skF_2'
      | ~ v1_funct_2(A_4,'#skF_2',B_176)
      | ~ r1_tarski(A_4,k2_zfmisc_1('#skF_2',B_176)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8228,c_8228,c_8228,c_8228,c_1000])).

tff(c_8852,plain,(
    ! [B_176,A_4] :
      ( k1_relset_1('#skF_1',B_176,A_4) = '#skF_1'
      | ~ v1_funct_2(A_4,'#skF_1',B_176)
      | ~ r1_tarski(A_4,k2_zfmisc_1('#skF_1',B_176)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8667,c_8667,c_8667,c_8667,c_8233])).

tff(c_8974,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_8697,c_8852])).

tff(c_8997,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8700,c_8974])).

tff(c_8693,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8667,c_577])).

tff(c_9052,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8997,c_8693])).

tff(c_9054,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8229,c_9052])).

tff(c_9055,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8665])).

tff(c_5225,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1235])).

tff(c_5227,plain,(
    ~ v2_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_5225])).

tff(c_8236,plain,(
    ~ v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8228,c_5227])).

tff(c_9074,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9055,c_8236])).

tff(c_9093,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_9074])).

tff(c_9095,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5225])).

tff(c_9094,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5225])).

tff(c_9160,plain,(
    ! [B_647] :
      ( k10_relat_1(B_647,k9_relat_1(B_647,k1_relat_1(B_647))) = k1_relat_1(B_647)
      | ~ v2_funct_1(B_647)
      | ~ v1_funct_1(B_647)
      | ~ v1_relat_1(B_647) ) ),
    inference(resolution,[status(thm)],[c_6,c_1148])).

tff(c_9179,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_9160])).

tff(c_9185,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_5226,c_9095,c_9094,c_9179])).

tff(c_12249,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12242,c_12242,c_9185])).

tff(c_13211,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13197,c_13197,c_12249])).

tff(c_54,plain,(
    ! [B_32,A_31] :
      ( m1_subset_1(B_32,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_32),A_31)))
      | ~ r1_tarski(k2_relat_1(B_32),A_31)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_13358,plain,(
    ! [A_31] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_31)))
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_31)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13211,c_54])).

tff(c_13375,plain,(
    ! [A_31] : m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_31))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_70,c_13216,c_13224,c_13358])).

tff(c_14276,plain,(
    ! [A_893] :
      ( v5_relat_1(k2_funct_1(A_893),k1_relat_1(A_893))
      | ~ v1_relat_1(k2_funct_1(A_893))
      | ~ v2_funct_1(A_893)
      | ~ v1_funct_1(A_893)
      | ~ v1_relat_1(A_893) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_211])).

tff(c_14279,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13211,c_14276])).

tff(c_14284,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_70,c_64,c_14279])).

tff(c_14285,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_14284])).

tff(c_14311,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_14285])).

tff(c_14315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_70,c_14311])).

tff(c_14317,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_14284])).

tff(c_14316,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_14284])).

tff(c_12285,plain,(
    ! [A_791] : r1_tarski('#skF_2',A_791) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12242,c_8])).

tff(c_12316,plain,(
    ! [B_84] :
      ( k2_relat_1(B_84) = '#skF_2'
      | ~ v5_relat_1(B_84,'#skF_2')
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_12285,c_339])).

tff(c_13770,plain,(
    ! [B_84] :
      ( k2_relat_1(B_84) = '#skF_3'
      | ~ v5_relat_1(B_84,'#skF_3')
      | ~ v1_relat_1(B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13197,c_13197,c_12316])).

tff(c_14320,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14316,c_13770])).

tff(c_14323,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14317,c_14320])).

tff(c_56,plain,(
    ! [B_32,A_31] :
      ( v1_funct_2(B_32,k1_relat_1(B_32),A_31)
      | ~ r1_tarski(k2_relat_1(B_32),A_31)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_13220,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13197,c_12242])).

tff(c_44,plain,(
    ! [C_30,A_28] :
      ( k1_xboole_0 = C_30
      | ~ v1_funct_2(C_30,A_28,k1_xboole_0)
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1064,plain,(
    ! [B_183] :
      ( k1_xboole_0 = B_183
      | ~ v1_funct_2(B_183,k1_relat_1(B_183),k1_xboole_0)
      | k1_relat_1(B_183) = k1_xboole_0
      | ~ r1_tarski(k2_relat_1(B_183),k1_xboole_0)
      | ~ v1_funct_1(B_183)
      | ~ v1_relat_1(B_183) ) ),
    inference(resolution,[status(thm)],[c_1038,c_44])).

tff(c_15799,plain,(
    ! [B_1014] :
      ( B_1014 = '#skF_3'
      | ~ v1_funct_2(B_1014,k1_relat_1(B_1014),'#skF_3')
      | k1_relat_1(B_1014) = '#skF_3'
      | ~ r1_tarski(k2_relat_1(B_1014),'#skF_3')
      | ~ v1_funct_1(B_1014)
      | ~ v1_relat_1(B_1014) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13220,c_13220,c_13220,c_13220,c_1064])).

tff(c_16275,plain,(
    ! [B_1023] :
      ( B_1023 = '#skF_3'
      | k1_relat_1(B_1023) = '#skF_3'
      | ~ r1_tarski(k2_relat_1(B_1023),'#skF_3')
      | ~ v1_funct_1(B_1023)
      | ~ v1_relat_1(B_1023) ) ),
    inference(resolution,[status(thm)],[c_56,c_15799])).

tff(c_16285,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14323,c_16275])).

tff(c_16314,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14317,c_137,c_13216,c_16285])).

tff(c_16325,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_16314])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1070,plain,(
    ! [B_183,A_184] :
      ( r1_tarski(B_183,k2_zfmisc_1(k1_relat_1(B_183),A_184))
      | ~ r1_tarski(k2_relat_1(B_183),A_184)
      | ~ v1_funct_1(B_183)
      | ~ v1_relat_1(B_183) ) ),
    inference(resolution,[status(thm)],[c_1038,c_10])).

tff(c_16351,plain,(
    ! [A_184] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3',A_184))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_184)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16325,c_1070])).

tff(c_16393,plain,(
    ! [A_184] : r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3',A_184)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14317,c_137,c_13216,c_14323,c_16351])).

tff(c_152,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_138])).

tff(c_13227,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13197,c_152])).

tff(c_16506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16393,c_13227])).

tff(c_16507,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_16314])).

tff(c_13228,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13197,c_138])).

tff(c_16521,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16507,c_13228])).

tff(c_16538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13375,c_16521])).

tff(c_16539,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_16540,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_17229,plain,(
    ! [A_1125,B_1126,C_1127] :
      ( k1_relset_1(A_1125,B_1126,C_1127) = k1_relat_1(C_1127)
      | ~ m1_subset_1(C_1127,k1_zfmisc_1(k2_zfmisc_1(A_1125,B_1126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_17240,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16540,c_17229])).

tff(c_17738,plain,(
    ! [B_1173,C_1174,A_1175] :
      ( k1_xboole_0 = B_1173
      | v1_funct_2(C_1174,A_1175,B_1173)
      | k1_relset_1(A_1175,B_1173,C_1174) != A_1175
      | ~ m1_subset_1(C_1174,k1_zfmisc_1(k2_zfmisc_1(A_1175,B_1173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_17744,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_16540,c_17738])).

tff(c_17754,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17240,c_17744])).

tff(c_17755,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_16539,c_17754])).

tff(c_17759,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_17755])).

tff(c_17762,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_17759])).

tff(c_17765,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16568,c_70,c_64,c_17105,c_17762])).

tff(c_17766,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_17755])).

tff(c_17792,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17766,c_8])).

tff(c_16566,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16540,c_16555])).

tff(c_16739,plain,(
    ! [C_1061,B_1062,A_1063] :
      ( v5_relat_1(C_1061,B_1062)
      | ~ m1_subset_1(C_1061,k1_zfmisc_1(k2_zfmisc_1(A_1063,B_1062))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_16750,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_16540,c_16739])).

tff(c_16648,plain,(
    ! [B_1046,A_1047] :
      ( r1_tarski(k2_relat_1(B_1046),A_1047)
      | ~ v5_relat_1(B_1046,A_1047)
      | ~ v1_relat_1(B_1046) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16590,plain,(
    ! [B_1036,A_1037] :
      ( B_1036 = A_1037
      | ~ r1_tarski(B_1036,A_1037)
      | ~ r1_tarski(A_1037,B_1036) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16601,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_16590])).

tff(c_16659,plain,(
    ! [B_1046] :
      ( k2_relat_1(B_1046) = k1_xboole_0
      | ~ v5_relat_1(B_1046,k1_xboole_0)
      | ~ v1_relat_1(B_1046) ) ),
    inference(resolution,[status(thm)],[c_16648,c_16601])).

tff(c_18184,plain,(
    ! [B_1195] :
      ( k2_relat_1(B_1195) = '#skF_1'
      | ~ v5_relat_1(B_1195,'#skF_1')
      | ~ v1_relat_1(B_1195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17766,c_17766,c_16659])).

tff(c_18211,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16750,c_18184])).

tff(c_18232,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16566,c_18211])).

tff(c_17767,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_17755])).

tff(c_17975,plain,(
    ! [A_31] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_31)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_31)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17767,c_56])).

tff(c_17995,plain,(
    ! [A_31] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_31)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16566,c_137,c_17975])).

tff(c_18652,plain,(
    ! [A_31] : v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17792,c_18232,c_17995])).

tff(c_18655,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18652,c_16539])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:55:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.41/3.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.66/3.79  
% 10.66/3.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.66/3.79  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.66/3.79  
% 10.66/3.79  %Foreground sorts:
% 10.66/3.79  
% 10.66/3.79  
% 10.66/3.79  %Background operators:
% 10.66/3.79  
% 10.66/3.79  
% 10.66/3.79  %Foreground operators:
% 10.66/3.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.66/3.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.66/3.79  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.66/3.79  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.66/3.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.66/3.79  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.66/3.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.66/3.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.66/3.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.66/3.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.66/3.79  tff('#skF_2', type, '#skF_2': $i).
% 10.66/3.79  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.66/3.79  tff('#skF_3', type, '#skF_3': $i).
% 10.66/3.79  tff('#skF_1', type, '#skF_1': $i).
% 10.66/3.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.66/3.79  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.66/3.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.66/3.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.66/3.79  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.66/3.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.66/3.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.66/3.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.66/3.79  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.66/3.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.66/3.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.66/3.79  
% 10.85/3.82  tff(f_146, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 10.85/3.82  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.85/3.82  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.85/3.82  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 10.85/3.82  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.85/3.82  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.85/3.82  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.85/3.82  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.85/3.82  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 10.85/3.82  tff(f_129, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 10.85/3.82  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.85/3.82  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.85/3.82  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.85/3.82  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 10.85/3.82  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 10.85/3.82  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 10.85/3.82  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.85/3.82  tff(c_16555, plain, (![C_1030, A_1031, B_1032]: (v1_relat_1(C_1030) | ~m1_subset_1(C_1030, k1_zfmisc_1(k2_zfmisc_1(A_1031, B_1032))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.85/3.82  tff(c_16568, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_16555])).
% 10.85/3.82  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.85/3.82  tff(c_64, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.85/3.82  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.85/3.82  tff(c_17091, plain, (![A_1109, B_1110, C_1111]: (k2_relset_1(A_1109, B_1110, C_1111)=k2_relat_1(C_1111) | ~m1_subset_1(C_1111, k1_zfmisc_1(k2_zfmisc_1(A_1109, B_1110))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.85/3.82  tff(c_17101, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_17091])).
% 10.85/3.82  tff(c_17105, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_17101])).
% 10.85/3.82  tff(c_30, plain, (![A_15]: (k1_relat_1(k2_funct_1(A_15))=k2_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.85/3.82  tff(c_153, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.85/3.82  tff(c_162, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_153])).
% 10.85/3.82  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.85/3.82  tff(c_24, plain, (![A_12]: (v1_relat_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.85/3.82  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.85/3.82  tff(c_568, plain, (![A_118, B_119, C_120]: (k1_relset_1(A_118, B_119, C_120)=k1_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.85/3.82  tff(c_577, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_568])).
% 10.85/3.82  tff(c_9313, plain, (![B_654, A_655, C_656]: (k1_xboole_0=B_654 | k1_relset_1(A_655, B_654, C_656)=A_655 | ~v1_funct_2(C_656, A_655, B_654) | ~m1_subset_1(C_656, k1_zfmisc_1(k2_zfmisc_1(A_655, B_654))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.85/3.82  tff(c_9326, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_9313])).
% 10.85/3.82  tff(c_9334, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_577, c_9326])).
% 10.85/3.82  tff(c_9335, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_9334])).
% 10.85/3.82  tff(c_402, plain, (![A_91]: (k2_relat_1(k2_funct_1(A_91))=k1_relat_1(A_91) | ~v2_funct_1(A_91) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.85/3.82  tff(c_206, plain, (![B_61, A_62]: (v5_relat_1(B_61, A_62) | ~r1_tarski(k2_relat_1(B_61), A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.85/3.82  tff(c_211, plain, (![B_61]: (v5_relat_1(B_61, k2_relat_1(B_61)) | ~v1_relat_1(B_61))), inference(resolution, [status(thm)], [c_6, c_206])).
% 10.85/3.82  tff(c_9778, plain, (![A_676]: (v5_relat_1(k2_funct_1(A_676), k1_relat_1(A_676)) | ~v1_relat_1(k2_funct_1(A_676)) | ~v2_funct_1(A_676) | ~v1_funct_1(A_676) | ~v1_relat_1(A_676))), inference(superposition, [status(thm), theory('equality')], [c_402, c_211])).
% 10.85/3.82  tff(c_9781, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9335, c_9778])).
% 10.85/3.82  tff(c_9789, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_70, c_64, c_9781])).
% 10.85/3.82  tff(c_9792, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_9789])).
% 10.85/3.82  tff(c_9795, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_9792])).
% 10.85/3.82  tff(c_9799, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_70, c_9795])).
% 10.85/3.82  tff(c_9801, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_9789])).
% 10.85/3.82  tff(c_81, plain, (![A_38]: (v1_funct_1(k2_funct_1(A_38)) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.85/3.82  tff(c_60, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.85/3.82  tff(c_80, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_60])).
% 10.85/3.82  tff(c_84, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_81, c_80])).
% 10.85/3.82  tff(c_87, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_84])).
% 10.85/3.82  tff(c_123, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.85/3.82  tff(c_130, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_123])).
% 10.85/3.82  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_130])).
% 10.85/3.82  tff(c_137, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_60])).
% 10.85/3.82  tff(c_9800, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_9789])).
% 10.85/3.82  tff(c_16, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.85/3.82  tff(c_10938, plain, (![A_760, A_761]: (r1_tarski(k1_relat_1(A_760), A_761) | ~v5_relat_1(k2_funct_1(A_760), A_761) | ~v1_relat_1(k2_funct_1(A_760)) | ~v2_funct_1(A_760) | ~v1_funct_1(A_760) | ~v1_relat_1(A_760))), inference(superposition, [status(thm), theory('equality')], [c_402, c_16])).
% 10.85/3.82  tff(c_10961, plain, (![A_762]: (r1_tarski(k1_relat_1(A_762), k2_relat_1(k2_funct_1(A_762))) | ~v2_funct_1(A_762) | ~v1_funct_1(A_762) | ~v1_relat_1(A_762) | ~v1_relat_1(k2_funct_1(A_762)))), inference(resolution, [status(thm)], [c_211, c_10938])).
% 10.85/3.82  tff(c_10972, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_9335, c_10961])).
% 10.85/3.82  tff(c_10987, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_9801, c_162, c_70, c_64, c_10972])).
% 10.85/3.82  tff(c_310, plain, (![B_84, A_85]: (r1_tarski(k2_relat_1(B_84), A_85) | ~v5_relat_1(B_84, A_85) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.85/3.82  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.85/3.82  tff(c_339, plain, (![B_84, A_85]: (k2_relat_1(B_84)=A_85 | ~r1_tarski(A_85, k2_relat_1(B_84)) | ~v5_relat_1(B_84, A_85) | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_310, c_2])).
% 10.85/3.82  tff(c_10993, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_10987, c_339])).
% 10.85/3.82  tff(c_11001, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9801, c_9800, c_10993])).
% 10.85/3.82  tff(c_661, plain, (![A_133, B_134, C_135]: (k2_relset_1(A_133, B_134, C_135)=k2_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.85/3.82  tff(c_668, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_661])).
% 10.85/3.82  tff(c_671, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_668])).
% 10.85/3.82  tff(c_1038, plain, (![B_183, A_184]: (m1_subset_1(B_183, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_183), A_184))) | ~r1_tarski(k2_relat_1(B_183), A_184) | ~v1_funct_1(B_183) | ~v1_relat_1(B_183))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.85/3.82  tff(c_12112, plain, (![A_788, A_789]: (m1_subset_1(k2_funct_1(A_788), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_788), A_789))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_788)), A_789) | ~v1_funct_1(k2_funct_1(A_788)) | ~v1_relat_1(k2_funct_1(A_788)) | ~v2_funct_1(A_788) | ~v1_funct_1(A_788) | ~v1_relat_1(A_788))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1038])).
% 10.85/3.82  tff(c_12155, plain, (![A_789]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_789))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_789) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_671, c_12112])).
% 10.85/3.82  tff(c_12196, plain, (![A_790]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_790))) | ~r1_tarski('#skF_1', A_790))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_70, c_64, c_9801, c_137, c_11001, c_12155])).
% 10.85/3.82  tff(c_136, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_60])).
% 10.85/3.82  tff(c_138, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_136])).
% 10.85/3.82  tff(c_12224, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_12196, c_138])).
% 10.85/3.82  tff(c_12241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_12224])).
% 10.85/3.82  tff(c_12243, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_9334])).
% 10.85/3.82  tff(c_140, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.85/3.82  tff(c_148, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_140])).
% 10.85/3.82  tff(c_12242, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_9334])).
% 10.85/3.82  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.85/3.82  tff(c_855, plain, (![C_162, A_163]: (k1_xboole_0=C_162 | ~v1_funct_2(C_162, A_163, k1_xboole_0) | k1_xboole_0=A_163 | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_163, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.85/3.82  tff(c_860, plain, (![A_4, A_163]: (k1_xboole_0=A_4 | ~v1_funct_2(A_4, A_163, k1_xboole_0) | k1_xboole_0=A_163 | ~r1_tarski(A_4, k2_zfmisc_1(A_163, k1_xboole_0)))), inference(resolution, [status(thm)], [c_12, c_855])).
% 10.85/3.82  tff(c_12665, plain, (![A_809, A_810]: (A_809='#skF_2' | ~v1_funct_2(A_809, A_810, '#skF_2') | A_810='#skF_2' | ~r1_tarski(A_809, k2_zfmisc_1(A_810, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_12242, c_12242, c_12242, c_12242, c_860])).
% 10.85/3.82  tff(c_12676, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_148, c_12665])).
% 10.85/3.82  tff(c_12686, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_12676])).
% 10.85/3.82  tff(c_12688, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_12686])).
% 10.85/3.82  tff(c_12722, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12688, c_68])).
% 10.85/3.82  tff(c_12719, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12688, c_148])).
% 10.85/3.82  tff(c_995, plain, (![B_176, C_177]: (k1_relset_1(k1_xboole_0, B_176, C_177)=k1_xboole_0 | ~v1_funct_2(C_177, k1_xboole_0, B_176) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_176))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.85/3.82  tff(c_1000, plain, (![B_176, A_4]: (k1_relset_1(k1_xboole_0, B_176, A_4)=k1_xboole_0 | ~v1_funct_2(A_4, k1_xboole_0, B_176) | ~r1_tarski(A_4, k2_zfmisc_1(k1_xboole_0, B_176)))), inference(resolution, [status(thm)], [c_12, c_995])).
% 10.85/3.82  tff(c_12245, plain, (![B_176, A_4]: (k1_relset_1('#skF_2', B_176, A_4)='#skF_2' | ~v1_funct_2(A_4, '#skF_2', B_176) | ~r1_tarski(A_4, k2_zfmisc_1('#skF_2', B_176)))), inference(demodulation, [status(thm), theory('equality')], [c_12242, c_12242, c_12242, c_12242, c_1000])).
% 10.85/3.82  tff(c_13055, plain, (![B_176, A_4]: (k1_relset_1('#skF_1', B_176, A_4)='#skF_1' | ~v1_funct_2(A_4, '#skF_1', B_176) | ~r1_tarski(A_4, k2_zfmisc_1('#skF_1', B_176)))), inference(demodulation, [status(thm), theory('equality')], [c_12688, c_12688, c_12688, c_12688, c_12245])).
% 10.85/3.82  tff(c_13078, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_12719, c_13055])).
% 10.85/3.82  tff(c_13101, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12722, c_13078])).
% 10.85/3.82  tff(c_12715, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12688, c_577])).
% 10.85/3.82  tff(c_13195, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13101, c_12715])).
% 10.85/3.82  tff(c_13196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12243, c_13195])).
% 10.85/3.82  tff(c_13197, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_12686])).
% 10.85/3.82  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.85/3.82  tff(c_12277, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_12242, c_8])).
% 10.85/3.82  tff(c_13216, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_13197, c_12277])).
% 10.85/3.82  tff(c_13224, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13197, c_671])).
% 10.85/3.82  tff(c_163, plain, (![A_53, A_54, B_55]: (v1_relat_1(A_53) | ~r1_tarski(A_53, k2_zfmisc_1(A_54, B_55)))), inference(resolution, [status(thm)], [c_12, c_153])).
% 10.85/3.82  tff(c_177, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_163])).
% 10.85/3.82  tff(c_1237, plain, (![B_195, A_196, C_197]: (k1_xboole_0=B_195 | k1_relset_1(A_196, B_195, C_197)=A_196 | ~v1_funct_2(C_197, A_196, B_195) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_196, B_195))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.85/3.82  tff(c_1247, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_1237])).
% 10.85/3.82  tff(c_1252, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_577, c_1247])).
% 10.85/3.82  tff(c_1253, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1252])).
% 10.85/3.82  tff(c_1722, plain, (![A_228]: (v5_relat_1(k2_funct_1(A_228), k1_relat_1(A_228)) | ~v1_relat_1(k2_funct_1(A_228)) | ~v2_funct_1(A_228) | ~v1_funct_1(A_228) | ~v1_relat_1(A_228))), inference(superposition, [status(thm), theory('equality')], [c_402, c_211])).
% 10.85/3.82  tff(c_1725, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1253, c_1722])).
% 10.85/3.82  tff(c_1730, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_70, c_64, c_1725])).
% 10.85/3.82  tff(c_1731, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1730])).
% 10.85/3.82  tff(c_1734, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_1731])).
% 10.85/3.82  tff(c_1738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_70, c_1734])).
% 10.85/3.82  tff(c_1740, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1730])).
% 10.85/3.82  tff(c_1739, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_1730])).
% 10.85/3.82  tff(c_2939, plain, (![A_324, A_325]: (r1_tarski(k1_relat_1(A_324), A_325) | ~v5_relat_1(k2_funct_1(A_324), A_325) | ~v1_relat_1(k2_funct_1(A_324)) | ~v2_funct_1(A_324) | ~v1_funct_1(A_324) | ~v1_relat_1(A_324))), inference(superposition, [status(thm), theory('equality')], [c_402, c_16])).
% 10.85/3.82  tff(c_2962, plain, (![A_327]: (r1_tarski(k1_relat_1(A_327), k2_relat_1(k2_funct_1(A_327))) | ~v2_funct_1(A_327) | ~v1_funct_1(A_327) | ~v1_relat_1(A_327) | ~v1_relat_1(k2_funct_1(A_327)))), inference(resolution, [status(thm)], [c_211, c_2939])).
% 10.85/3.82  tff(c_2970, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1253, c_2962])).
% 10.85/3.82  tff(c_2980, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1740, c_162, c_70, c_64, c_2970])).
% 10.85/3.82  tff(c_2984, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2980, c_339])).
% 10.85/3.82  tff(c_2992, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1740, c_1739, c_2984])).
% 10.85/3.82  tff(c_4094, plain, (![A_371, A_372]: (m1_subset_1(k2_funct_1(A_371), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_371), A_372))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_371)), A_372) | ~v1_funct_1(k2_funct_1(A_371)) | ~v1_relat_1(k2_funct_1(A_371)) | ~v2_funct_1(A_371) | ~v1_funct_1(A_371) | ~v1_relat_1(A_371))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1038])).
% 10.85/3.82  tff(c_4134, plain, (![A_372]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_372))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_372) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_671, c_4094])).
% 10.85/3.82  tff(c_4173, plain, (![A_373]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_373))) | ~r1_tarski('#skF_1', A_373))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_70, c_64, c_1740, c_137, c_2992, c_4134])).
% 10.85/3.82  tff(c_4201, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_4173, c_138])).
% 10.85/3.82  tff(c_4218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4201])).
% 10.85/3.82  tff(c_4220, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_1252])).
% 10.85/3.82  tff(c_4219, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1252])).
% 10.85/3.82  tff(c_4739, plain, (![A_408, A_409]: (A_408='#skF_2' | ~v1_funct_2(A_408, A_409, '#skF_2') | A_409='#skF_2' | ~r1_tarski(A_408, k2_zfmisc_1(A_409, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4219, c_4219, c_4219, c_4219, c_860])).
% 10.85/3.82  tff(c_4750, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_148, c_4739])).
% 10.85/3.82  tff(c_4760, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4750])).
% 10.85/3.82  tff(c_4762, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_4760])).
% 10.85/3.82  tff(c_4797, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4762, c_68])).
% 10.85/3.82  tff(c_4794, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4762, c_148])).
% 10.85/3.82  tff(c_4786, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4762, c_4219])).
% 10.85/3.82  tff(c_5000, plain, (![B_176, A_4]: (k1_relset_1('#skF_1', B_176, A_4)='#skF_1' | ~v1_funct_2(A_4, '#skF_1', B_176) | ~r1_tarski(A_4, k2_zfmisc_1('#skF_1', B_176)))), inference(demodulation, [status(thm), theory('equality')], [c_4786, c_4786, c_4786, c_4786, c_1000])).
% 10.85/3.82  tff(c_5076, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_4794, c_5000])).
% 10.85/3.82  tff(c_5096, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4797, c_5076])).
% 10.85/3.82  tff(c_4790, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4762, c_577])).
% 10.85/3.82  tff(c_5182, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5096, c_4790])).
% 10.85/3.82  tff(c_5183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4220, c_5182])).
% 10.85/3.82  tff(c_5184, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_4760])).
% 10.85/3.82  tff(c_214, plain, (![C_66, B_67, A_68]: (v5_relat_1(C_66, B_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_68, B_67))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.85/3.82  tff(c_224, plain, (![A_69, B_70, A_71]: (v5_relat_1(A_69, B_70) | ~r1_tarski(A_69, k2_zfmisc_1(A_71, B_70)))), inference(resolution, [status(thm)], [c_12, c_214])).
% 10.85/3.82  tff(c_238, plain, (![B_70]: (v5_relat_1(k1_xboole_0, B_70))), inference(resolution, [status(thm)], [c_8, c_224])).
% 10.85/3.82  tff(c_179, plain, (![B_56, A_57]: (B_56=A_57 | ~r1_tarski(B_56, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.85/3.82  tff(c_187, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_179])).
% 10.85/3.82  tff(c_367, plain, (![B_90]: (k2_relat_1(B_90)=k1_xboole_0 | ~v5_relat_1(B_90, k1_xboole_0) | ~v1_relat_1(B_90))), inference(resolution, [status(thm)], [c_310, c_187])).
% 10.85/3.82  tff(c_375, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_238, c_367])).
% 10.85/3.82  tff(c_381, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_177, c_375])).
% 10.85/3.82  tff(c_243, plain, (![C_75, A_76, B_77]: (v4_relat_1(C_75, A_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.85/3.82  tff(c_287, plain, (![A_80, A_81, B_82]: (v4_relat_1(A_80, A_81) | ~r1_tarski(A_80, k2_zfmisc_1(A_81, B_82)))), inference(resolution, [status(thm)], [c_12, c_243])).
% 10.85/3.82  tff(c_303, plain, (![A_83]: (v4_relat_1(k1_xboole_0, A_83))), inference(resolution, [status(thm)], [c_8, c_287])).
% 10.85/3.82  tff(c_20, plain, (![B_11, A_10]: (k7_relat_1(B_11, A_10)=B_11 | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.85/3.82  tff(c_306, plain, (![A_83]: (k7_relat_1(k1_xboole_0, A_83)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_303, c_20])).
% 10.85/3.82  tff(c_341, plain, (![A_86]: (k7_relat_1(k1_xboole_0, A_86)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_177, c_306])).
% 10.85/3.82  tff(c_18, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.85/3.82  tff(c_346, plain, (![A_86]: (k9_relat_1(k1_xboole_0, A_86)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_341, c_18])).
% 10.85/3.82  tff(c_351, plain, (![A_86]: (k9_relat_1(k1_xboole_0, A_86)=k2_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_346])).
% 10.85/3.82  tff(c_382, plain, (![A_86]: (k9_relat_1(k1_xboole_0, A_86)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_381, c_351])).
% 10.85/3.82  tff(c_1148, plain, (![B_190, A_191]: (k10_relat_1(B_190, k9_relat_1(B_190, A_191))=A_191 | ~v2_funct_1(B_190) | ~r1_tarski(A_191, k1_relat_1(B_190)) | ~v1_funct_1(B_190) | ~v1_relat_1(B_190))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.85/3.82  tff(c_1215, plain, (![B_194]: (k10_relat_1(B_194, k9_relat_1(B_194, k1_xboole_0))=k1_xboole_0 | ~v2_funct_1(B_194) | ~v1_funct_1(B_194) | ~v1_relat_1(B_194))), inference(resolution, [status(thm)], [c_8, c_1148])).
% 10.85/3.82  tff(c_1229, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_382, c_1215])).
% 10.85/3.82  tff(c_1235, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_177, c_1229])).
% 10.85/3.82  tff(c_1236, plain, (~v1_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1235])).
% 10.85/3.82  tff(c_4221, plain, (~v1_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4219, c_1236])).
% 10.85/3.82  tff(c_5207, plain, (~v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5184, c_4221])).
% 10.85/3.82  tff(c_5224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_5207])).
% 10.85/3.82  tff(c_5226, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_1235])).
% 10.85/3.82  tff(c_5382, plain, (![B_439, A_440, C_441]: (k1_xboole_0=B_439 | k1_relset_1(A_440, B_439, C_441)=A_440 | ~v1_funct_2(C_441, A_440, B_439) | ~m1_subset_1(C_441, k1_zfmisc_1(k2_zfmisc_1(A_440, B_439))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.85/3.82  tff(c_5392, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_5382])).
% 10.85/3.82  tff(c_5397, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_577, c_5392])).
% 10.85/3.82  tff(c_5398, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_5397])).
% 10.85/3.82  tff(c_5637, plain, (![A_452]: (v5_relat_1(k2_funct_1(A_452), k1_relat_1(A_452)) | ~v1_relat_1(k2_funct_1(A_452)) | ~v2_funct_1(A_452) | ~v1_funct_1(A_452) | ~v1_relat_1(A_452))), inference(superposition, [status(thm), theory('equality')], [c_402, c_211])).
% 10.85/3.82  tff(c_5640, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5398, c_5637])).
% 10.85/3.82  tff(c_5645, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_70, c_64, c_5640])).
% 10.85/3.82  tff(c_5682, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5645])).
% 10.85/3.82  tff(c_5685, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_5682])).
% 10.85/3.82  tff(c_5689, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_70, c_5685])).
% 10.85/3.82  tff(c_5691, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5645])).
% 10.85/3.82  tff(c_5690, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_5645])).
% 10.85/3.82  tff(c_6868, plain, (![A_541, A_542]: (r1_tarski(k1_relat_1(A_541), A_542) | ~v5_relat_1(k2_funct_1(A_541), A_542) | ~v1_relat_1(k2_funct_1(A_541)) | ~v2_funct_1(A_541) | ~v1_funct_1(A_541) | ~v1_relat_1(A_541))), inference(superposition, [status(thm), theory('equality')], [c_402, c_16])).
% 10.85/3.82  tff(c_7011, plain, (![A_555]: (r1_tarski(k1_relat_1(A_555), k2_relat_1(k2_funct_1(A_555))) | ~v2_funct_1(A_555) | ~v1_funct_1(A_555) | ~v1_relat_1(A_555) | ~v1_relat_1(k2_funct_1(A_555)))), inference(resolution, [status(thm)], [c_211, c_6868])).
% 10.85/3.82  tff(c_7019, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5398, c_7011])).
% 10.85/3.82  tff(c_7029, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5691, c_162, c_70, c_64, c_7019])).
% 10.85/3.82  tff(c_7033, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7029, c_339])).
% 10.85/3.82  tff(c_7041, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5691, c_5690, c_7033])).
% 10.85/3.82  tff(c_8103, plain, (![A_599, A_600]: (m1_subset_1(k2_funct_1(A_599), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_599), A_600))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_599)), A_600) | ~v1_funct_1(k2_funct_1(A_599)) | ~v1_relat_1(k2_funct_1(A_599)) | ~v2_funct_1(A_599) | ~v1_funct_1(A_599) | ~v1_relat_1(A_599))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1038])).
% 10.85/3.82  tff(c_8143, plain, (![A_600]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_600))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_600) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_671, c_8103])).
% 10.85/3.82  tff(c_8182, plain, (![A_601]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_601))) | ~r1_tarski('#skF_1', A_601))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_70, c_64, c_5691, c_137, c_7041, c_8143])).
% 10.85/3.82  tff(c_8210, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_8182, c_138])).
% 10.85/3.82  tff(c_8227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_8210])).
% 10.85/3.82  tff(c_8229, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_5397])).
% 10.85/3.82  tff(c_8228, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_5397])).
% 10.85/3.82  tff(c_8639, plain, (![A_622, A_623]: (A_622='#skF_2' | ~v1_funct_2(A_622, A_623, '#skF_2') | A_623='#skF_2' | ~r1_tarski(A_622, k2_zfmisc_1(A_623, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_8228, c_8228, c_8228, c_8228, c_860])).
% 10.85/3.82  tff(c_8654, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_148, c_8639])).
% 10.85/3.82  tff(c_8665, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_8654])).
% 10.85/3.82  tff(c_8667, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_8665])).
% 10.85/3.82  tff(c_8700, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8667, c_68])).
% 10.85/3.82  tff(c_8697, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8667, c_148])).
% 10.85/3.82  tff(c_8233, plain, (![B_176, A_4]: (k1_relset_1('#skF_2', B_176, A_4)='#skF_2' | ~v1_funct_2(A_4, '#skF_2', B_176) | ~r1_tarski(A_4, k2_zfmisc_1('#skF_2', B_176)))), inference(demodulation, [status(thm), theory('equality')], [c_8228, c_8228, c_8228, c_8228, c_1000])).
% 10.85/3.82  tff(c_8852, plain, (![B_176, A_4]: (k1_relset_1('#skF_1', B_176, A_4)='#skF_1' | ~v1_funct_2(A_4, '#skF_1', B_176) | ~r1_tarski(A_4, k2_zfmisc_1('#skF_1', B_176)))), inference(demodulation, [status(thm), theory('equality')], [c_8667, c_8667, c_8667, c_8667, c_8233])).
% 10.85/3.82  tff(c_8974, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_8697, c_8852])).
% 10.85/3.83  tff(c_8997, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8700, c_8974])).
% 10.85/3.83  tff(c_8693, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8667, c_577])).
% 10.85/3.83  tff(c_9052, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8997, c_8693])).
% 10.85/3.83  tff(c_9054, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8229, c_9052])).
% 10.85/3.83  tff(c_9055, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_8665])).
% 10.85/3.83  tff(c_5225, plain, (~v2_funct_1(k1_xboole_0) | k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_1235])).
% 10.85/3.83  tff(c_5227, plain, (~v2_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_5225])).
% 10.85/3.83  tff(c_8236, plain, (~v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8228, c_5227])).
% 10.85/3.83  tff(c_9074, plain, (~v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9055, c_8236])).
% 10.85/3.83  tff(c_9093, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_9074])).
% 10.85/3.83  tff(c_9095, plain, (v2_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_5225])).
% 10.85/3.83  tff(c_9094, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_5225])).
% 10.85/3.83  tff(c_9160, plain, (![B_647]: (k10_relat_1(B_647, k9_relat_1(B_647, k1_relat_1(B_647)))=k1_relat_1(B_647) | ~v2_funct_1(B_647) | ~v1_funct_1(B_647) | ~v1_relat_1(B_647))), inference(resolution, [status(thm)], [c_6, c_1148])).
% 10.85/3.83  tff(c_9179, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_382, c_9160])).
% 10.85/3.83  tff(c_9185, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_177, c_5226, c_9095, c_9094, c_9179])).
% 10.85/3.83  tff(c_12249, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12242, c_12242, c_9185])).
% 10.85/3.83  tff(c_13211, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13197, c_13197, c_12249])).
% 10.85/3.83  tff(c_54, plain, (![B_32, A_31]: (m1_subset_1(B_32, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_32), A_31))) | ~r1_tarski(k2_relat_1(B_32), A_31) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.85/3.83  tff(c_13358, plain, (![A_31]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_31))) | ~r1_tarski(k2_relat_1('#skF_3'), A_31) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_13211, c_54])).
% 10.85/3.83  tff(c_13375, plain, (![A_31]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_31))))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_70, c_13216, c_13224, c_13358])).
% 10.85/3.83  tff(c_14276, plain, (![A_893]: (v5_relat_1(k2_funct_1(A_893), k1_relat_1(A_893)) | ~v1_relat_1(k2_funct_1(A_893)) | ~v2_funct_1(A_893) | ~v1_funct_1(A_893) | ~v1_relat_1(A_893))), inference(superposition, [status(thm), theory('equality')], [c_402, c_211])).
% 10.85/3.83  tff(c_14279, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13211, c_14276])).
% 10.85/3.83  tff(c_14284, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_70, c_64, c_14279])).
% 10.85/3.83  tff(c_14285, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_14284])).
% 10.85/3.83  tff(c_14311, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_14285])).
% 10.85/3.83  tff(c_14315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_70, c_14311])).
% 10.85/3.83  tff(c_14317, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_14284])).
% 10.85/3.83  tff(c_14316, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_14284])).
% 10.85/3.83  tff(c_12285, plain, (![A_791]: (r1_tarski('#skF_2', A_791))), inference(demodulation, [status(thm), theory('equality')], [c_12242, c_8])).
% 10.85/3.83  tff(c_12316, plain, (![B_84]: (k2_relat_1(B_84)='#skF_2' | ~v5_relat_1(B_84, '#skF_2') | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_12285, c_339])).
% 10.85/3.83  tff(c_13770, plain, (![B_84]: (k2_relat_1(B_84)='#skF_3' | ~v5_relat_1(B_84, '#skF_3') | ~v1_relat_1(B_84))), inference(demodulation, [status(thm), theory('equality')], [c_13197, c_13197, c_12316])).
% 10.85/3.83  tff(c_14320, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_14316, c_13770])).
% 10.85/3.83  tff(c_14323, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14317, c_14320])).
% 10.85/3.83  tff(c_56, plain, (![B_32, A_31]: (v1_funct_2(B_32, k1_relat_1(B_32), A_31) | ~r1_tarski(k2_relat_1(B_32), A_31) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.85/3.83  tff(c_13220, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13197, c_12242])).
% 10.85/3.83  tff(c_44, plain, (![C_30, A_28]: (k1_xboole_0=C_30 | ~v1_funct_2(C_30, A_28, k1_xboole_0) | k1_xboole_0=A_28 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.85/3.83  tff(c_1064, plain, (![B_183]: (k1_xboole_0=B_183 | ~v1_funct_2(B_183, k1_relat_1(B_183), k1_xboole_0) | k1_relat_1(B_183)=k1_xboole_0 | ~r1_tarski(k2_relat_1(B_183), k1_xboole_0) | ~v1_funct_1(B_183) | ~v1_relat_1(B_183))), inference(resolution, [status(thm)], [c_1038, c_44])).
% 10.85/3.83  tff(c_15799, plain, (![B_1014]: (B_1014='#skF_3' | ~v1_funct_2(B_1014, k1_relat_1(B_1014), '#skF_3') | k1_relat_1(B_1014)='#skF_3' | ~r1_tarski(k2_relat_1(B_1014), '#skF_3') | ~v1_funct_1(B_1014) | ~v1_relat_1(B_1014))), inference(demodulation, [status(thm), theory('equality')], [c_13220, c_13220, c_13220, c_13220, c_1064])).
% 10.85/3.83  tff(c_16275, plain, (![B_1023]: (B_1023='#skF_3' | k1_relat_1(B_1023)='#skF_3' | ~r1_tarski(k2_relat_1(B_1023), '#skF_3') | ~v1_funct_1(B_1023) | ~v1_relat_1(B_1023))), inference(resolution, [status(thm)], [c_56, c_15799])).
% 10.85/3.83  tff(c_16285, plain, (k2_funct_1('#skF_3')='#skF_3' | k1_relat_1(k2_funct_1('#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14323, c_16275])).
% 10.85/3.83  tff(c_16314, plain, (k2_funct_1('#skF_3')='#skF_3' | k1_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14317, c_137, c_13216, c_16285])).
% 10.85/3.83  tff(c_16325, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(splitLeft, [status(thm)], [c_16314])).
% 10.85/3.83  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.85/3.83  tff(c_1070, plain, (![B_183, A_184]: (r1_tarski(B_183, k2_zfmisc_1(k1_relat_1(B_183), A_184)) | ~r1_tarski(k2_relat_1(B_183), A_184) | ~v1_funct_1(B_183) | ~v1_relat_1(B_183))), inference(resolution, [status(thm)], [c_1038, c_10])).
% 10.85/3.83  tff(c_16351, plain, (![A_184]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', A_184)) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_184) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_16325, c_1070])).
% 10.85/3.83  tff(c_16393, plain, (![A_184]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', A_184)))), inference(demodulation, [status(thm), theory('equality')], [c_14317, c_137, c_13216, c_14323, c_16351])).
% 10.85/3.83  tff(c_152, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_12, c_138])).
% 10.85/3.83  tff(c_13227, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_13197, c_152])).
% 10.85/3.83  tff(c_16506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16393, c_13227])).
% 10.85/3.83  tff(c_16507, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_16314])).
% 10.85/3.83  tff(c_13228, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_13197, c_138])).
% 10.85/3.83  tff(c_16521, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_16507, c_13228])).
% 10.85/3.83  tff(c_16538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13375, c_16521])).
% 10.85/3.83  tff(c_16539, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_136])).
% 10.85/3.83  tff(c_16540, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_136])).
% 10.85/3.83  tff(c_17229, plain, (![A_1125, B_1126, C_1127]: (k1_relset_1(A_1125, B_1126, C_1127)=k1_relat_1(C_1127) | ~m1_subset_1(C_1127, k1_zfmisc_1(k2_zfmisc_1(A_1125, B_1126))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.85/3.83  tff(c_17240, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_16540, c_17229])).
% 10.85/3.83  tff(c_17738, plain, (![B_1173, C_1174, A_1175]: (k1_xboole_0=B_1173 | v1_funct_2(C_1174, A_1175, B_1173) | k1_relset_1(A_1175, B_1173, C_1174)!=A_1175 | ~m1_subset_1(C_1174, k1_zfmisc_1(k2_zfmisc_1(A_1175, B_1173))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.85/3.83  tff(c_17744, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_16540, c_17738])).
% 10.85/3.83  tff(c_17754, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_17240, c_17744])).
% 10.85/3.83  tff(c_17755, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_16539, c_17754])).
% 10.85/3.83  tff(c_17759, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_17755])).
% 10.85/3.83  tff(c_17762, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_17759])).
% 10.85/3.83  tff(c_17765, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16568, c_70, c_64, c_17105, c_17762])).
% 10.85/3.83  tff(c_17766, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_17755])).
% 10.85/3.83  tff(c_17792, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_17766, c_8])).
% 10.85/3.83  tff(c_16566, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_16540, c_16555])).
% 10.85/3.83  tff(c_16739, plain, (![C_1061, B_1062, A_1063]: (v5_relat_1(C_1061, B_1062) | ~m1_subset_1(C_1061, k1_zfmisc_1(k2_zfmisc_1(A_1063, B_1062))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.85/3.83  tff(c_16750, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_16540, c_16739])).
% 10.85/3.83  tff(c_16648, plain, (![B_1046, A_1047]: (r1_tarski(k2_relat_1(B_1046), A_1047) | ~v5_relat_1(B_1046, A_1047) | ~v1_relat_1(B_1046))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.85/3.83  tff(c_16590, plain, (![B_1036, A_1037]: (B_1036=A_1037 | ~r1_tarski(B_1036, A_1037) | ~r1_tarski(A_1037, B_1036))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.85/3.83  tff(c_16601, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_16590])).
% 10.85/3.83  tff(c_16659, plain, (![B_1046]: (k2_relat_1(B_1046)=k1_xboole_0 | ~v5_relat_1(B_1046, k1_xboole_0) | ~v1_relat_1(B_1046))), inference(resolution, [status(thm)], [c_16648, c_16601])).
% 10.85/3.83  tff(c_18184, plain, (![B_1195]: (k2_relat_1(B_1195)='#skF_1' | ~v5_relat_1(B_1195, '#skF_1') | ~v1_relat_1(B_1195))), inference(demodulation, [status(thm), theory('equality')], [c_17766, c_17766, c_16659])).
% 10.85/3.83  tff(c_18211, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_16750, c_18184])).
% 10.85/3.83  tff(c_18232, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16566, c_18211])).
% 10.85/3.83  tff(c_17767, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_17755])).
% 10.85/3.83  tff(c_17975, plain, (![A_31]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_31) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_31) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_17767, c_56])).
% 10.85/3.83  tff(c_17995, plain, (![A_31]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_31) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_31))), inference(demodulation, [status(thm), theory('equality')], [c_16566, c_137, c_17975])).
% 10.85/3.83  tff(c_18652, plain, (![A_31]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_31))), inference(demodulation, [status(thm), theory('equality')], [c_17792, c_18232, c_17995])).
% 10.85/3.83  tff(c_18655, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18652, c_16539])).
% 10.85/3.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.85/3.83  
% 10.85/3.83  Inference rules
% 10.85/3.83  ----------------------
% 10.85/3.83  #Ref     : 0
% 10.85/3.83  #Sup     : 3578
% 10.85/3.83  #Fact    : 0
% 10.85/3.83  #Define  : 0
% 10.85/3.83  #Split   : 50
% 10.85/3.83  #Chain   : 0
% 10.85/3.83  #Close   : 0
% 10.85/3.83  
% 10.85/3.83  Ordering : KBO
% 10.85/3.83  
% 10.85/3.83  Simplification rules
% 10.85/3.83  ----------------------
% 10.85/3.83  #Subsume      : 483
% 10.85/3.83  #Demod        : 6374
% 10.85/3.83  #Tautology    : 1913
% 10.85/3.83  #SimpNegUnit  : 20
% 10.85/3.83  #BackRed      : 411
% 10.85/3.83  
% 10.85/3.83  #Partial instantiations: 0
% 10.85/3.83  #Strategies tried      : 1
% 10.85/3.83  
% 10.85/3.83  Timing (in seconds)
% 10.85/3.83  ----------------------
% 10.85/3.83  Preprocessing        : 0.34
% 10.85/3.83  Parsing              : 0.18
% 10.85/3.83  CNF conversion       : 0.02
% 10.85/3.83  Main loop            : 2.67
% 10.85/3.83  Inferencing          : 0.87
% 10.85/3.83  Reduction            : 1.07
% 10.85/3.83  Demodulation         : 0.82
% 10.85/3.83  BG Simplification    : 0.08
% 10.85/3.83  Subsumption          : 0.46
% 10.85/3.83  Abstraction          : 0.11
% 10.85/3.83  MUC search           : 0.00
% 10.85/3.83  Cooper               : 0.00
% 10.85/3.83  Total                : 3.11
% 10.85/3.83  Index Insertion      : 0.00
% 10.85/3.83  Index Deletion       : 0.00
% 10.85/3.83  Index Matching       : 0.00
% 10.85/3.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
