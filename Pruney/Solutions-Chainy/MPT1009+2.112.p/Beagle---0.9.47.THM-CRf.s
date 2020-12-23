%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:57 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 317 expanded)
%              Number of leaves         :   41 ( 122 expanded)
%              Depth                    :   13
%              Number of atoms          :  148 ( 642 expanded)
%              Number of equality atoms :   52 ( 165 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_42,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_139,plain,(
    ! [B_51,A_52] :
      ( v1_relat_1(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_142,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_139])).

tff(c_148,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_142])).

tff(c_44,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k9_relat_1(B_28,A_27),k2_relat_1(B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_48,plain,(
    ! [A_29] :
      ( k1_relat_1(A_29) != k1_xboole_0
      | k1_xboole_0 = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_158,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_148,c_48])).

tff(c_160,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_445,plain,(
    ! [B_102,A_103] :
      ( k1_tarski(k1_funct_1(B_102,A_103)) = k2_relat_1(B_102)
      | k1_tarski(A_103) != k1_relat_1(B_102)
      | ~ v1_funct_1(B_102)
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_58,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_454,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_58])).

tff(c_460,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_66,c_454])).

tff(c_521,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_460])).

tff(c_338,plain,(
    ! [C_83,A_84,B_85] :
      ( v4_relat_1(C_83,A_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_352,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_338])).

tff(c_306,plain,(
    ! [B_77,A_78] :
      ( r1_tarski(k1_relat_1(B_77),A_78)
      | ~ v4_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k1_tarski(B_11) = A_10
      | k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_tarski(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_546,plain,(
    ! [B_113,B_114] :
      ( k1_tarski(B_113) = k1_relat_1(B_114)
      | k1_relat_1(B_114) = k1_xboole_0
      | ~ v4_relat_1(B_114,k1_tarski(B_113))
      | ~ v1_relat_1(B_114) ) ),
    inference(resolution,[status(thm)],[c_306,c_16])).

tff(c_552,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_352,c_546])).

tff(c_559,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_552])).

tff(c_561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_521,c_559])).

tff(c_563,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_460])).

tff(c_567,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_62])).

tff(c_56,plain,(
    ! [A_35,B_36,C_37,D_38] :
      ( k7_relset_1(A_35,B_36,C_37,D_38) = k9_relat_1(C_37,D_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_607,plain,(
    ! [D_38] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_38) = k9_relat_1('#skF_4',D_38) ),
    inference(resolution,[status(thm)],[c_567,c_56])).

tff(c_562,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_460])).

tff(c_617,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_562])).

tff(c_618,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_617])).

tff(c_630,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_618])).

tff(c_634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_630])).

tff(c_635,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_46,plain,(
    ! [A_29] :
      ( k2_relat_1(A_29) != k1_xboole_0
      | k1_xboole_0 = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_157,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_148,c_46])).

tff(c_159,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_637,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_159])).

tff(c_28,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_642,plain,(
    ! [A_14] : m1_subset_1('#skF_4',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_28])).

tff(c_790,plain,(
    ! [C_145,B_146,A_147] :
      ( v5_relat_1(C_145,B_146)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_802,plain,(
    ! [B_148] : v5_relat_1('#skF_4',B_148) ),
    inference(resolution,[status(thm)],[c_642,c_790])).

tff(c_761,plain,(
    ! [B_140,A_141] :
      ( r1_tarski(k2_relat_1(B_140),A_141)
      | ~ v5_relat_1(B_140,A_141)
      | ~ v1_relat_1(B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_658,plain,(
    ! [A_126] : r1_tarski('#skF_4',A_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_661,plain,(
    ! [A_126] :
      ( A_126 = '#skF_4'
      | ~ r1_tarski(A_126,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_658,c_2])).

tff(c_768,plain,(
    ! [B_140] :
      ( k2_relat_1(B_140) = '#skF_4'
      | ~ v5_relat_1(B_140,'#skF_4')
      | ~ v1_relat_1(B_140) ) ),
    inference(resolution,[status(thm)],[c_761,c_661])).

tff(c_806,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_802,c_768])).

tff(c_809,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_806])).

tff(c_811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_637,c_809])).

tff(c_812,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_820,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_812,c_8])).

tff(c_813,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_830,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_812,c_813])).

tff(c_893,plain,(
    ! [B_156,A_157] :
      ( r1_tarski(k9_relat_1(B_156,A_157),k2_relat_1(B_156))
      | ~ v1_relat_1(B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_896,plain,(
    ! [A_157] :
      ( r1_tarski(k9_relat_1('#skF_4',A_157),'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_893])).

tff(c_898,plain,(
    ! [A_157] : r1_tarski(k9_relat_1('#skF_4',A_157),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_896])).

tff(c_910,plain,(
    ! [B_160,A_161] :
      ( B_160 = A_161
      | ~ r1_tarski(B_160,A_161)
      | ~ r1_tarski(A_161,B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_912,plain,(
    ! [A_157] :
      ( k9_relat_1('#skF_4',A_157) = '#skF_4'
      | ~ r1_tarski('#skF_4',k9_relat_1('#skF_4',A_157)) ) ),
    inference(resolution,[status(thm)],[c_898,c_910])).

tff(c_921,plain,(
    ! [A_157] : k9_relat_1('#skF_4',A_157) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_912])).

tff(c_818,plain,(
    ! [A_14] : m1_subset_1('#skF_4',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_812,c_28])).

tff(c_1170,plain,(
    ! [A_205,B_206,C_207,D_208] :
      ( k7_relset_1(A_205,B_206,C_207,D_208) = k9_relat_1(C_207,D_208)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1173,plain,(
    ! [A_205,B_206,D_208] : k7_relset_1(A_205,B_206,'#skF_4',D_208) = k9_relat_1('#skF_4',D_208) ),
    inference(resolution,[status(thm)],[c_818,c_1170])).

tff(c_1179,plain,(
    ! [A_205,B_206,D_208] : k7_relset_1(A_205,B_206,'#skF_4',D_208) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_1173])).

tff(c_1180,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1179,c_58])).

tff(c_1183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_1180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.52  
% 2.96/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.96/1.52  
% 2.96/1.52  %Foreground sorts:
% 2.96/1.52  
% 2.96/1.52  
% 2.96/1.52  %Background operators:
% 2.96/1.52  
% 2.96/1.52  
% 2.96/1.52  %Foreground operators:
% 2.96/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.96/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.96/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.96/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.96/1.52  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.96/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.96/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.96/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.96/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.96/1.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.96/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.52  tff('#skF_1', type, '#skF_1': $i).
% 2.96/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.96/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.96/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.96/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.96/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.96/1.52  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.96/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.96/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.96/1.52  
% 3.28/1.54  tff(f_80, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.28/1.54  tff(f_122, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.28/1.54  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.28/1.54  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.28/1.54  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.28/1.54  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.28/1.54  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.28/1.54  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.28/1.54  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.28/1.54  tff(f_110, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.28/1.54  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.28/1.54  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.28/1.54  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.28/1.54  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.28/1.54  tff(c_42, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.28/1.54  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.28/1.54  tff(c_139, plain, (![B_51, A_52]: (v1_relat_1(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.28/1.54  tff(c_142, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_139])).
% 3.28/1.54  tff(c_148, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_142])).
% 3.28/1.54  tff(c_44, plain, (![B_28, A_27]: (r1_tarski(k9_relat_1(B_28, A_27), k2_relat_1(B_28)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.28/1.54  tff(c_48, plain, (![A_29]: (k1_relat_1(A_29)!=k1_xboole_0 | k1_xboole_0=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.28/1.54  tff(c_158, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_148, c_48])).
% 3.28/1.54  tff(c_160, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_158])).
% 3.28/1.54  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.28/1.54  tff(c_445, plain, (![B_102, A_103]: (k1_tarski(k1_funct_1(B_102, A_103))=k2_relat_1(B_102) | k1_tarski(A_103)!=k1_relat_1(B_102) | ~v1_funct_1(B_102) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.28/1.54  tff(c_58, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.28/1.54  tff(c_454, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_445, c_58])).
% 3.28/1.54  tff(c_460, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_66, c_454])).
% 3.28/1.54  tff(c_521, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_460])).
% 3.28/1.54  tff(c_338, plain, (![C_83, A_84, B_85]: (v4_relat_1(C_83, A_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.28/1.54  tff(c_352, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_338])).
% 3.28/1.54  tff(c_306, plain, (![B_77, A_78]: (r1_tarski(k1_relat_1(B_77), A_78) | ~v4_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.28/1.54  tff(c_16, plain, (![B_11, A_10]: (k1_tarski(B_11)=A_10 | k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.28/1.54  tff(c_546, plain, (![B_113, B_114]: (k1_tarski(B_113)=k1_relat_1(B_114) | k1_relat_1(B_114)=k1_xboole_0 | ~v4_relat_1(B_114, k1_tarski(B_113)) | ~v1_relat_1(B_114))), inference(resolution, [status(thm)], [c_306, c_16])).
% 3.28/1.54  tff(c_552, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_352, c_546])).
% 3.28/1.54  tff(c_559, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_148, c_552])).
% 3.28/1.54  tff(c_561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_521, c_559])).
% 3.28/1.54  tff(c_563, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_460])).
% 3.28/1.54  tff(c_567, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_563, c_62])).
% 3.28/1.54  tff(c_56, plain, (![A_35, B_36, C_37, D_38]: (k7_relset_1(A_35, B_36, C_37, D_38)=k9_relat_1(C_37, D_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.28/1.54  tff(c_607, plain, (![D_38]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_38)=k9_relat_1('#skF_4', D_38))), inference(resolution, [status(thm)], [c_567, c_56])).
% 3.28/1.54  tff(c_562, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_460])).
% 3.28/1.54  tff(c_617, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_563, c_562])).
% 3.28/1.54  tff(c_618, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_607, c_617])).
% 3.28/1.54  tff(c_630, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_618])).
% 3.28/1.54  tff(c_634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_630])).
% 3.28/1.54  tff(c_635, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_158])).
% 3.28/1.54  tff(c_46, plain, (![A_29]: (k2_relat_1(A_29)!=k1_xboole_0 | k1_xboole_0=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.28/1.54  tff(c_157, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_148, c_46])).
% 3.28/1.54  tff(c_159, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_157])).
% 3.28/1.54  tff(c_637, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_635, c_159])).
% 3.28/1.54  tff(c_28, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.28/1.54  tff(c_642, plain, (![A_14]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_635, c_28])).
% 3.28/1.54  tff(c_790, plain, (![C_145, B_146, A_147]: (v5_relat_1(C_145, B_146) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_147, B_146))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.28/1.54  tff(c_802, plain, (![B_148]: (v5_relat_1('#skF_4', B_148))), inference(resolution, [status(thm)], [c_642, c_790])).
% 3.28/1.54  tff(c_761, plain, (![B_140, A_141]: (r1_tarski(k2_relat_1(B_140), A_141) | ~v5_relat_1(B_140, A_141) | ~v1_relat_1(B_140))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.28/1.54  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.28/1.54  tff(c_658, plain, (![A_126]: (r1_tarski('#skF_4', A_126))), inference(demodulation, [status(thm), theory('equality')], [c_635, c_8])).
% 3.28/1.54  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.28/1.54  tff(c_661, plain, (![A_126]: (A_126='#skF_4' | ~r1_tarski(A_126, '#skF_4'))), inference(resolution, [status(thm)], [c_658, c_2])).
% 3.28/1.54  tff(c_768, plain, (![B_140]: (k2_relat_1(B_140)='#skF_4' | ~v5_relat_1(B_140, '#skF_4') | ~v1_relat_1(B_140))), inference(resolution, [status(thm)], [c_761, c_661])).
% 3.28/1.54  tff(c_806, plain, (k2_relat_1('#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_802, c_768])).
% 3.28/1.54  tff(c_809, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_806])).
% 3.28/1.54  tff(c_811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_637, c_809])).
% 3.28/1.54  tff(c_812, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_157])).
% 3.28/1.54  tff(c_820, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_812, c_8])).
% 3.28/1.54  tff(c_813, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_157])).
% 3.28/1.54  tff(c_830, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_812, c_813])).
% 3.28/1.54  tff(c_893, plain, (![B_156, A_157]: (r1_tarski(k9_relat_1(B_156, A_157), k2_relat_1(B_156)) | ~v1_relat_1(B_156))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.28/1.54  tff(c_896, plain, (![A_157]: (r1_tarski(k9_relat_1('#skF_4', A_157), '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_830, c_893])).
% 3.28/1.54  tff(c_898, plain, (![A_157]: (r1_tarski(k9_relat_1('#skF_4', A_157), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_896])).
% 3.28/1.54  tff(c_910, plain, (![B_160, A_161]: (B_160=A_161 | ~r1_tarski(B_160, A_161) | ~r1_tarski(A_161, B_160))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.28/1.54  tff(c_912, plain, (![A_157]: (k9_relat_1('#skF_4', A_157)='#skF_4' | ~r1_tarski('#skF_4', k9_relat_1('#skF_4', A_157)))), inference(resolution, [status(thm)], [c_898, c_910])).
% 3.28/1.54  tff(c_921, plain, (![A_157]: (k9_relat_1('#skF_4', A_157)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_820, c_912])).
% 3.28/1.54  tff(c_818, plain, (![A_14]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_812, c_28])).
% 3.28/1.54  tff(c_1170, plain, (![A_205, B_206, C_207, D_208]: (k7_relset_1(A_205, B_206, C_207, D_208)=k9_relat_1(C_207, D_208) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.28/1.54  tff(c_1173, plain, (![A_205, B_206, D_208]: (k7_relset_1(A_205, B_206, '#skF_4', D_208)=k9_relat_1('#skF_4', D_208))), inference(resolution, [status(thm)], [c_818, c_1170])).
% 3.28/1.54  tff(c_1179, plain, (![A_205, B_206, D_208]: (k7_relset_1(A_205, B_206, '#skF_4', D_208)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_921, c_1173])).
% 3.28/1.54  tff(c_1180, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1179, c_58])).
% 3.28/1.54  tff(c_1183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_820, c_1180])).
% 3.28/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.54  
% 3.28/1.54  Inference rules
% 3.28/1.54  ----------------------
% 3.28/1.54  #Ref     : 0
% 3.28/1.54  #Sup     : 224
% 3.28/1.54  #Fact    : 0
% 3.28/1.54  #Define  : 0
% 3.28/1.54  #Split   : 4
% 3.28/1.54  #Chain   : 0
% 3.28/1.54  #Close   : 0
% 3.28/1.54  
% 3.28/1.54  Ordering : KBO
% 3.28/1.54  
% 3.28/1.54  Simplification rules
% 3.28/1.54  ----------------------
% 3.28/1.54  #Subsume      : 11
% 3.28/1.54  #Demod        : 176
% 3.28/1.54  #Tautology    : 143
% 3.28/1.54  #SimpNegUnit  : 2
% 3.28/1.54  #BackRed      : 26
% 3.28/1.54  
% 3.28/1.54  #Partial instantiations: 0
% 3.28/1.54  #Strategies tried      : 1
% 3.28/1.54  
% 3.28/1.54  Timing (in seconds)
% 3.28/1.54  ----------------------
% 3.28/1.54  Preprocessing        : 0.34
% 3.28/1.54  Parsing              : 0.19
% 3.28/1.54  CNF conversion       : 0.02
% 3.28/1.54  Main loop            : 0.38
% 3.28/1.54  Inferencing          : 0.14
% 3.28/1.54  Reduction            : 0.12
% 3.28/1.54  Demodulation         : 0.09
% 3.28/1.54  BG Simplification    : 0.02
% 3.28/1.54  Subsumption          : 0.06
% 3.28/1.54  Abstraction          : 0.02
% 3.28/1.54  MUC search           : 0.00
% 3.28/1.54  Cooper               : 0.00
% 3.28/1.55  Total                : 0.76
% 3.28/1.55  Index Insertion      : 0.00
% 3.28/1.55  Index Deletion       : 0.00
% 3.28/1.55  Index Matching       : 0.00
% 3.28/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
