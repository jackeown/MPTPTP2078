%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:35 EST 2020

% Result     : Theorem 9.61s
% Output     : CNFRefutation 9.71s
% Verified   : 
% Statistics : Number of formulae       :  210 (3738 expanded)
%              Number of leaves         :   40 (1096 expanded)
%              Depth                    :   15
%              Number of atoms          :  356 (11413 expanded)
%              Number of equality atoms :   87 (4326 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_120,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v5_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc22_relat_1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_132,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(c_74,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_10505,plain,(
    ! [C_946,A_947,B_948] :
      ( v1_relat_1(C_946)
      | ~ m1_subset_1(C_946,k1_zfmisc_1(k2_zfmisc_1(A_947,B_948))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10518,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_10505])).

tff(c_72,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_88,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_78,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_11125,plain,(
    ! [A_1031,B_1032,C_1033] :
      ( k1_relset_1(A_1031,B_1032,C_1033) = k1_relat_1(C_1033)
      | ~ m1_subset_1(C_1033,k1_zfmisc_1(k2_zfmisc_1(A_1031,B_1032))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_11144,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_11125])).

tff(c_11769,plain,(
    ! [B_1117,A_1118,C_1119] :
      ( k1_xboole_0 = B_1117
      | k1_relset_1(A_1118,B_1117,C_1119) = A_1118
      | ~ v1_funct_2(C_1119,A_1118,B_1117)
      | ~ m1_subset_1(C_1119,k1_zfmisc_1(k2_zfmisc_1(A_1118,B_1117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_11779,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_11769])).

tff(c_11790,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_11144,c_11779])).

tff(c_11791,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_11790])).

tff(c_32,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(k7_relat_1(B_18,A_17)) = A_17
      | ~ r1_tarski(A_17,k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_11806,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_2')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11791,c_32])).

tff(c_11816,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10518,c_11806])).

tff(c_80,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_11726,plain,(
    ! [A_1111,B_1112,C_1113,D_1114] :
      ( k2_partfun1(A_1111,B_1112,C_1113,D_1114) = k7_relat_1(C_1113,D_1114)
      | ~ m1_subset_1(C_1113,k1_zfmisc_1(k2_zfmisc_1(A_1111,B_1112)))
      | ~ v1_funct_1(C_1113) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_11735,plain,(
    ! [D_1114] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_1114) = k7_relat_1('#skF_5',D_1114)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_76,c_11726])).

tff(c_11747,plain,(
    ! [D_1114] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_1114) = k7_relat_1('#skF_5',D_1114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_11735])).

tff(c_995,plain,(
    ! [C_180,A_181,B_182] :
      ( v1_relat_1(C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1008,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_995])).

tff(c_1098,plain,(
    ! [C_200,B_201,A_202] :
      ( v5_relat_1(C_200,B_201)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_202,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1113,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1098])).

tff(c_1163,plain,(
    ! [C_213,A_214,B_215] :
      ( v1_relat_1(k7_relat_1(C_213,A_214))
      | ~ v5_relat_1(C_213,B_215)
      | ~ v1_relat_1(C_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1171,plain,(
    ! [A_214] :
      ( v1_relat_1(k7_relat_1('#skF_5',A_214))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1113,c_1163])).

tff(c_1183,plain,(
    ! [A_214] : v1_relat_1(k7_relat_1('#skF_5',A_214)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_1171])).

tff(c_4947,plain,(
    ! [A_548,B_549,C_550,D_551] :
      ( k2_partfun1(A_548,B_549,C_550,D_551) = k7_relat_1(C_550,D_551)
      | ~ m1_subset_1(C_550,k1_zfmisc_1(k2_zfmisc_1(A_548,B_549)))
      | ~ v1_funct_1(C_550) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4954,plain,(
    ! [D_551] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_551) = k7_relat_1('#skF_5',D_551)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_76,c_4947])).

tff(c_4963,plain,(
    ! [D_551] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_551) = k7_relat_1('#skF_5',D_551) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4954])).

tff(c_5382,plain,(
    ! [A_588,B_589,C_590,D_591] :
      ( m1_subset_1(k2_partfun1(A_588,B_589,C_590,D_591),k1_zfmisc_1(k2_zfmisc_1(A_588,B_589)))
      | ~ m1_subset_1(C_590,k1_zfmisc_1(k2_zfmisc_1(A_588,B_589)))
      | ~ v1_funct_1(C_590) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_5410,plain,(
    ! [D_551] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_551),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4963,c_5382])).

tff(c_5443,plain,(
    ! [D_593] : m1_subset_1(k7_relat_1('#skF_5',D_593),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_5410])).

tff(c_40,plain,(
    ! [C_27,B_26,A_25] :
      ( v5_relat_1(C_27,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5483,plain,(
    ! [D_593] : v5_relat_1(k7_relat_1('#skF_5',D_593),'#skF_3') ),
    inference(resolution,[status(thm)],[c_5443,c_40])).

tff(c_28,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4684,plain,(
    ! [A_510,B_511,C_512,D_513] :
      ( v1_funct_1(k2_partfun1(A_510,B_511,C_512,D_513))
      | ~ m1_subset_1(C_512,k1_zfmisc_1(k2_zfmisc_1(A_510,B_511)))
      | ~ v1_funct_1(C_512) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4689,plain,(
    ! [D_513] :
      ( v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5',D_513))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_76,c_4684])).

tff(c_4697,plain,(
    ! [D_513] : v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5',D_513)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4689])).

tff(c_4964,plain,(
    ! [D_513] : v1_funct_1(k7_relat_1('#skF_5',D_513)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4963,c_4697])).

tff(c_1460,plain,(
    ! [A_254,B_255,C_256] :
      ( k1_relset_1(A_254,B_255,C_256) = k1_relat_1(C_256)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1475,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_1460])).

tff(c_5157,plain,(
    ! [B_581,A_582,C_583] :
      ( k1_xboole_0 = B_581
      | k1_relset_1(A_582,B_581,C_583) = A_582
      | ~ v1_funct_2(C_583,A_582,B_581)
      | ~ m1_subset_1(C_583,k1_zfmisc_1(k2_zfmisc_1(A_582,B_581))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_5167,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_5157])).

tff(c_5178,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1475,c_5167])).

tff(c_5179,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_5178])).

tff(c_5194,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_2')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5179,c_32])).

tff(c_5269,plain,(
    ! [A_586] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_586)) = A_586
      | ~ r1_tarski(A_586,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_5194])).

tff(c_64,plain,(
    ! [B_43,A_42] :
      ( m1_subset_1(B_43,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_43),A_42)))
      | ~ r1_tarski(k2_relat_1(B_43),A_42)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_5278,plain,(
    ! [A_586,A_42] :
      ( m1_subset_1(k7_relat_1('#skF_5',A_586),k1_zfmisc_1(k2_zfmisc_1(A_586,A_42)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5',A_586)),A_42)
      | ~ v1_funct_1(k7_relat_1('#skF_5',A_586))
      | ~ v1_relat_1(k7_relat_1('#skF_5',A_586))
      | ~ r1_tarski(A_586,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5269,c_64])).

tff(c_10410,plain,(
    ! [A_943,A_944] :
      ( m1_subset_1(k7_relat_1('#skF_5',A_943),k1_zfmisc_1(k2_zfmisc_1(A_943,A_944)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5',A_943)),A_944)
      | ~ r1_tarski(A_943,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1183,c_4964,c_5278])).

tff(c_915,plain,(
    ! [A_168,B_169,C_170,D_171] :
      ( v1_funct_1(k2_partfun1(A_168,B_169,C_170,D_171))
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169)))
      | ~ v1_funct_1(C_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_920,plain,(
    ! [D_171] :
      ( v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5',D_171))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_76,c_915])).

tff(c_928,plain,(
    ! [D_171] : v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5',D_171)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_920])).

tff(c_70,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_161,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_161])).

tff(c_932,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_982,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_932])).

tff(c_4966,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4963,c_982])).

tff(c_10425,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_4')),'#skF_3')
    | ~ r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_10410,c_4966])).

tff(c_10467,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_10425])).

tff(c_10486,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_28,c_10467])).

tff(c_10490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1183,c_5483,c_10486])).

tff(c_10492,plain,(
    m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_932])).

tff(c_11142,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) = k1_relat_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_10492,c_11125])).

tff(c_11750,plain,(
    k1_relset_1('#skF_4','#skF_3',k7_relat_1('#skF_5','#skF_4')) = k1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11747,c_11747,c_11142])).

tff(c_10491,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_932])).

tff(c_11757,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_4'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11747,c_10491])).

tff(c_11756,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11747,c_10492])).

tff(c_11925,plain,(
    ! [B_1121,C_1122,A_1123] :
      ( k1_xboole_0 = B_1121
      | v1_funct_2(C_1122,A_1123,B_1121)
      | k1_relset_1(A_1123,B_1121,C_1122) != A_1123
      | ~ m1_subset_1(C_1122,k1_zfmisc_1(k2_zfmisc_1(A_1123,B_1121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_11928,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_4'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_11756,c_11925])).

tff(c_11947,plain,(
    k1_relset_1('#skF_4','#skF_3',k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_11757,c_88,c_11928])).

tff(c_12035,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11750,c_11947])).

tff(c_12042,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11816,c_12035])).

tff(c_12046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_12042])).

tff(c_12048,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_12047,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_12054,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12048,c_12047])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12049,plain,(
    ! [A_8] : r1_tarski('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12047,c_14])).

tff(c_12065,plain,(
    ! [A_8] : r1_tarski('#skF_3',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12054,c_12049])).

tff(c_12060,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12054,c_74])).

tff(c_13589,plain,(
    ! [B_1337,A_1338] :
      ( B_1337 = A_1338
      | ~ r1_tarski(B_1337,A_1338)
      | ~ r1_tarski(A_1338,B_1337) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13595,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_12060,c_13589])).

tff(c_13606,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12065,c_13595])).

tff(c_20,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12067,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_3',B_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12048,c_12048,c_20])).

tff(c_12091,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12067,c_12054,c_76])).

tff(c_12092,plain,(
    ! [A_1129,B_1130] :
      ( r1_tarski(A_1129,B_1130)
      | ~ m1_subset_1(A_1129,k1_zfmisc_1(B_1130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12096,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_12091,c_12092])).

tff(c_13593,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_12096,c_13589])).

tff(c_13603,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12065,c_13593])).

tff(c_13640,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13606,c_13603])).

tff(c_12059,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12054,c_78])).

tff(c_13621,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13606,c_13606,c_12059])).

tff(c_13641,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13640,c_13621])).

tff(c_13618,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13606,c_12091])).

tff(c_13703,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13640,c_13618])).

tff(c_13620,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_4',B_10) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13606,c_13606,c_12067])).

tff(c_13901,plain,(
    ! [C_1376,B_1377,A_1378] :
      ( v5_relat_1(C_1376,B_1377)
      | ~ m1_subset_1(C_1376,k1_zfmisc_1(k2_zfmisc_1(A_1378,B_1377))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_13931,plain,(
    ! [C_1384,B_1385] :
      ( v5_relat_1(C_1384,B_1385)
      | ~ m1_subset_1(C_1384,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13620,c_13901])).

tff(c_13937,plain,(
    ! [B_1385] : v5_relat_1('#skF_4',B_1385) ),
    inference(resolution,[status(thm)],[c_13703,c_13931])).

tff(c_13643,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13640,c_80])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12075,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12048,c_12048,c_18])).

tff(c_12103,plain,(
    ! [C_1135,A_1136,B_1137] :
      ( v1_relat_1(C_1135)
      | ~ m1_subset_1(C_1135,k1_zfmisc_1(k2_zfmisc_1(A_1136,B_1137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12114,plain,(
    ! [C_1140] :
      ( v1_relat_1(C_1140)
      | ~ m1_subset_1(C_1140,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12075,c_12103])).

tff(c_12124,plain,(
    ! [A_1141] :
      ( v1_relat_1(A_1141)
      | ~ r1_tarski(A_1141,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_12114])).

tff(c_12146,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12060,c_12124])).

tff(c_30,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k7_relat_1(B_16,A_15),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_13607,plain,(
    ! [A_8] :
      ( A_8 = '#skF_3'
      | ~ r1_tarski(A_8,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12065,c_13589])).

tff(c_13713,plain,(
    ! [A_1345] :
      ( A_1345 = '#skF_4'
      | ~ r1_tarski(A_1345,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13606,c_13606,c_13607])).

tff(c_13721,plain,(
    ! [A_15] :
      ( k7_relat_1('#skF_4',A_15) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_13713])).

tff(c_13730,plain,(
    ! [A_15] : k7_relat_1('#skF_4',A_15) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12146,c_13721])).

tff(c_14783,plain,(
    ! [A_1496,B_1497,C_1498,D_1499] :
      ( k2_partfun1(A_1496,B_1497,C_1498,D_1499) = k7_relat_1(C_1498,D_1499)
      | ~ m1_subset_1(C_1498,k1_zfmisc_1(k2_zfmisc_1(A_1496,B_1497)))
      | ~ v1_funct_1(C_1498) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_16473,plain,(
    ! [B_1639,C_1640,D_1641] :
      ( k2_partfun1('#skF_4',B_1639,C_1640,D_1641) = k7_relat_1(C_1640,D_1641)
      | ~ m1_subset_1(C_1640,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_1640) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13620,c_14783])).

tff(c_16477,plain,(
    ! [B_1639,D_1641] :
      ( k2_partfun1('#skF_4',B_1639,'#skF_4',D_1641) = k7_relat_1('#skF_4',D_1641)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_13703,c_16473])).

tff(c_16484,plain,(
    ! [B_1639,D_1641] : k2_partfun1('#skF_4',B_1639,'#skF_4',D_1641) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13643,c_13730,c_16477])).

tff(c_14957,plain,(
    ! [A_1530,B_1531,C_1532,D_1533] :
      ( m1_subset_1(k2_partfun1(A_1530,B_1531,C_1532,D_1533),k1_zfmisc_1(k2_zfmisc_1(A_1530,B_1531)))
      | ~ m1_subset_1(C_1532,k1_zfmisc_1(k2_zfmisc_1(A_1530,B_1531)))
      | ~ v1_funct_1(C_1532) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_38,plain,(
    ! [C_24,A_22,B_23] :
      ( v1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_15711,plain,(
    ! [A_1572,B_1573,C_1574,D_1575] :
      ( v1_relat_1(k2_partfun1(A_1572,B_1573,C_1574,D_1575))
      | ~ m1_subset_1(C_1574,k1_zfmisc_1(k2_zfmisc_1(A_1572,B_1573)))
      | ~ v1_funct_1(C_1574) ) ),
    inference(resolution,[status(thm)],[c_14957,c_38])).

tff(c_15726,plain,(
    ! [B_1576,C_1577,D_1578] :
      ( v1_relat_1(k2_partfun1('#skF_4',B_1576,C_1577,D_1578))
      | ~ m1_subset_1(C_1577,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_1577) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13620,c_15711])).

tff(c_15730,plain,(
    ! [B_1576,D_1578] :
      ( v1_relat_1(k2_partfun1('#skF_4',B_1576,'#skF_4',D_1578))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_13703,c_15726])).

tff(c_15737,plain,(
    ! [B_1576,D_1578] : v1_relat_1(k2_partfun1('#skF_4',B_1576,'#skF_4',D_1578)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13643,c_15730])).

tff(c_13619,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13606,c_13606,c_12075])).

tff(c_14492,plain,(
    ! [A_1454,B_1455,C_1456,D_1457] :
      ( v1_funct_1(k2_partfun1(A_1454,B_1455,C_1456,D_1457))
      | ~ m1_subset_1(C_1456,k1_zfmisc_1(k2_zfmisc_1(A_1454,B_1455)))
      | ~ v1_funct_1(C_1456) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_14915,plain,(
    ! [A_1514,C_1515,D_1516] :
      ( v1_funct_1(k2_partfun1(A_1514,'#skF_4',C_1515,D_1516))
      | ~ m1_subset_1(C_1515,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_1515) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13619,c_14492])).

tff(c_14917,plain,(
    ! [A_1514,D_1516] :
      ( v1_funct_1(k2_partfun1(A_1514,'#skF_4','#skF_4',D_1516))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_13703,c_14915])).

tff(c_14923,plain,(
    ! [A_1514,D_1516] : v1_funct_1(k2_partfun1(A_1514,'#skF_4','#skF_4',D_1516)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13643,c_14917])).

tff(c_14652,plain,(
    ! [B_1480,A_1481] :
      ( m1_subset_1(B_1480,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1480),A_1481)))
      | ~ r1_tarski(k2_relat_1(B_1480),A_1481)
      | ~ v1_funct_1(B_1480)
      | ~ v1_relat_1(B_1480) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_15001,plain,(
    ! [B_1537] :
      ( m1_subset_1(B_1537,k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1(B_1537),'#skF_4')
      | ~ v1_funct_1(B_1537)
      | ~ v1_relat_1(B_1537) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13619,c_14652])).

tff(c_15012,plain,(
    ! [B_1538] :
      ( m1_subset_1(B_1538,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(B_1538)
      | ~ v5_relat_1(B_1538,'#skF_4')
      | ~ v1_relat_1(B_1538) ) ),
    inference(resolution,[status(thm)],[c_28,c_15001])).

tff(c_12190,plain,(
    ! [B_1150,A_1151] :
      ( B_1150 = A_1151
      | ~ r1_tarski(B_1150,A_1151)
      | ~ r1_tarski(A_1151,B_1150) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12196,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_12060,c_12190])).

tff(c_12207,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12065,c_12196])).

tff(c_12194,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_12096,c_12190])).

tff(c_12204,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12065,c_12194])).

tff(c_12241,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12207,c_12204])).

tff(c_12243,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12241,c_80])).

tff(c_12219,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12207,c_12091])).

tff(c_12281,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12241,c_12219])).

tff(c_12220,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12207,c_12207,c_12075])).

tff(c_13052,plain,(
    ! [A_1261,B_1262,C_1263,D_1264] :
      ( v1_funct_1(k2_partfun1(A_1261,B_1262,C_1263,D_1264))
      | ~ m1_subset_1(C_1263,k1_zfmisc_1(k2_zfmisc_1(A_1261,B_1262)))
      | ~ v1_funct_1(C_1263) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_13524,plain,(
    ! [A_1325,C_1326,D_1327] :
      ( v1_funct_1(k2_partfun1(A_1325,'#skF_4',C_1326,D_1327))
      | ~ m1_subset_1(C_1326,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_1326) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12220,c_13052])).

tff(c_13526,plain,(
    ! [A_1325,D_1327] :
      ( v1_funct_1(k2_partfun1(A_1325,'#skF_4','#skF_4',D_1327))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12281,c_13524])).

tff(c_13532,plain,(
    ! [A_1325,D_1327] : v1_funct_1(k2_partfun1(A_1325,'#skF_4','#skF_4',D_1327)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12243,c_13526])).

tff(c_12149,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ v1_funct_2(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12054,c_12054,c_12075,c_12054,c_70])).

tff(c_12150,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_12149])).

tff(c_12214,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12207,c_12207,c_12150])).

tff(c_12375,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12241,c_12214])).

tff(c_13554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13532,c_12375])).

tff(c_13555,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_12149])).

tff(c_13709,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13640,c_13606,c_13606,c_13606,c_13640,c_13606,c_13606,c_13606,c_13555])).

tff(c_13710,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_13709])).

tff(c_15029,plain,
    ( ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'))
    | ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_15012,c_13710])).

tff(c_15045,plain,
    ( ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14923,c_15029])).

tff(c_15256,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_15045])).

tff(c_15741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15737,c_15256])).

tff(c_15742,plain,(
    ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_15045])).

tff(c_16486,plain,(
    ~ v5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16484,c_15742])).

tff(c_16491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13937,c_16486])).

tff(c_16493,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_13709])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16581,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_16493,c_22])).

tff(c_16495,plain,(
    ! [A_8] :
      ( A_8 = '#skF_4'
      | ~ r1_tarski(A_8,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13606,c_13606,c_13607])).

tff(c_16599,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16581,c_16495])).

tff(c_16492,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_13709])).

tff(c_16616,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13641,c_16599,c_16492])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.61/3.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.71/3.47  
% 9.71/3.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.71/3.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.71/3.47  
% 9.71/3.47  %Foreground sorts:
% 9.71/3.47  
% 9.71/3.47  
% 9.71/3.47  %Background operators:
% 9.71/3.47  
% 9.71/3.47  
% 9.71/3.47  %Foreground operators:
% 9.71/3.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.71/3.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.71/3.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.71/3.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.71/3.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.71/3.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.71/3.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.71/3.47  tff('#skF_5', type, '#skF_5': $i).
% 9.71/3.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.71/3.47  tff('#skF_2', type, '#skF_2': $i).
% 9.71/3.47  tff('#skF_3', type, '#skF_3': $i).
% 9.71/3.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.71/3.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.71/3.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.71/3.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.71/3.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.71/3.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.71/3.47  tff('#skF_4', type, '#skF_4': $i).
% 9.71/3.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.71/3.47  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.71/3.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.71/3.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.71/3.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.71/3.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.71/3.47  
% 9.71/3.50  tff(f_152, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 9.71/3.50  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.71/3.50  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.71/3.50  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.71/3.50  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 9.71/3.50  tff(f_120, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.71/3.50  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.71/3.50  tff(f_74, axiom, (![A, B, C]: ((v1_relat_1(C) & v5_relat_1(C, B)) => (v1_relat_1(k7_relat_1(C, A)) & v5_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc22_relat_1)).
% 9.71/3.50  tff(f_114, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 9.71/3.50  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 9.71/3.50  tff(f_132, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 9.71/3.50  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.71/3.50  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.71/3.50  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.71/3.50  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.71/3.50  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 9.71/3.50  tff(c_74, plain, (r1_tarski('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.71/3.50  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.71/3.50  tff(c_10505, plain, (![C_946, A_947, B_948]: (v1_relat_1(C_946) | ~m1_subset_1(C_946, k1_zfmisc_1(k2_zfmisc_1(A_947, B_948))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.71/3.50  tff(c_10518, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_10505])).
% 9.71/3.50  tff(c_72, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.71/3.50  tff(c_88, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_72])).
% 9.71/3.50  tff(c_78, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.71/3.50  tff(c_11125, plain, (![A_1031, B_1032, C_1033]: (k1_relset_1(A_1031, B_1032, C_1033)=k1_relat_1(C_1033) | ~m1_subset_1(C_1033, k1_zfmisc_1(k2_zfmisc_1(A_1031, B_1032))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.71/3.50  tff(c_11144, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_11125])).
% 9.71/3.50  tff(c_11769, plain, (![B_1117, A_1118, C_1119]: (k1_xboole_0=B_1117 | k1_relset_1(A_1118, B_1117, C_1119)=A_1118 | ~v1_funct_2(C_1119, A_1118, B_1117) | ~m1_subset_1(C_1119, k1_zfmisc_1(k2_zfmisc_1(A_1118, B_1117))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.71/3.50  tff(c_11779, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_11769])).
% 9.71/3.50  tff(c_11790, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_11144, c_11779])).
% 9.71/3.50  tff(c_11791, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_88, c_11790])).
% 9.71/3.50  tff(c_32, plain, (![B_18, A_17]: (k1_relat_1(k7_relat_1(B_18, A_17))=A_17 | ~r1_tarski(A_17, k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.71/3.50  tff(c_11806, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_5', A_17))=A_17 | ~r1_tarski(A_17, '#skF_2') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_11791, c_32])).
% 9.71/3.50  tff(c_11816, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_5', A_17))=A_17 | ~r1_tarski(A_17, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10518, c_11806])).
% 9.71/3.50  tff(c_80, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.71/3.50  tff(c_11726, plain, (![A_1111, B_1112, C_1113, D_1114]: (k2_partfun1(A_1111, B_1112, C_1113, D_1114)=k7_relat_1(C_1113, D_1114) | ~m1_subset_1(C_1113, k1_zfmisc_1(k2_zfmisc_1(A_1111, B_1112))) | ~v1_funct_1(C_1113))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.71/3.50  tff(c_11735, plain, (![D_1114]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_1114)=k7_relat_1('#skF_5', D_1114) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_76, c_11726])).
% 9.71/3.50  tff(c_11747, plain, (![D_1114]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_1114)=k7_relat_1('#skF_5', D_1114))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_11735])).
% 9.71/3.50  tff(c_995, plain, (![C_180, A_181, B_182]: (v1_relat_1(C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.71/3.50  tff(c_1008, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_995])).
% 9.71/3.50  tff(c_1098, plain, (![C_200, B_201, A_202]: (v5_relat_1(C_200, B_201) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_202, B_201))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.71/3.50  tff(c_1113, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_1098])).
% 9.71/3.50  tff(c_1163, plain, (![C_213, A_214, B_215]: (v1_relat_1(k7_relat_1(C_213, A_214)) | ~v5_relat_1(C_213, B_215) | ~v1_relat_1(C_213))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.71/3.50  tff(c_1171, plain, (![A_214]: (v1_relat_1(k7_relat_1('#skF_5', A_214)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1113, c_1163])).
% 9.71/3.50  tff(c_1183, plain, (![A_214]: (v1_relat_1(k7_relat_1('#skF_5', A_214)))), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_1171])).
% 9.71/3.50  tff(c_4947, plain, (![A_548, B_549, C_550, D_551]: (k2_partfun1(A_548, B_549, C_550, D_551)=k7_relat_1(C_550, D_551) | ~m1_subset_1(C_550, k1_zfmisc_1(k2_zfmisc_1(A_548, B_549))) | ~v1_funct_1(C_550))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.71/3.50  tff(c_4954, plain, (![D_551]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_551)=k7_relat_1('#skF_5', D_551) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_76, c_4947])).
% 9.71/3.50  tff(c_4963, plain, (![D_551]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_551)=k7_relat_1('#skF_5', D_551))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4954])).
% 9.71/3.50  tff(c_5382, plain, (![A_588, B_589, C_590, D_591]: (m1_subset_1(k2_partfun1(A_588, B_589, C_590, D_591), k1_zfmisc_1(k2_zfmisc_1(A_588, B_589))) | ~m1_subset_1(C_590, k1_zfmisc_1(k2_zfmisc_1(A_588, B_589))) | ~v1_funct_1(C_590))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.71/3.50  tff(c_5410, plain, (![D_551]: (m1_subset_1(k7_relat_1('#skF_5', D_551), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4963, c_5382])).
% 9.71/3.50  tff(c_5443, plain, (![D_593]: (m1_subset_1(k7_relat_1('#skF_5', D_593), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_5410])).
% 9.71/3.50  tff(c_40, plain, (![C_27, B_26, A_25]: (v5_relat_1(C_27, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.71/3.50  tff(c_5483, plain, (![D_593]: (v5_relat_1(k7_relat_1('#skF_5', D_593), '#skF_3'))), inference(resolution, [status(thm)], [c_5443, c_40])).
% 9.71/3.50  tff(c_28, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.71/3.50  tff(c_4684, plain, (![A_510, B_511, C_512, D_513]: (v1_funct_1(k2_partfun1(A_510, B_511, C_512, D_513)) | ~m1_subset_1(C_512, k1_zfmisc_1(k2_zfmisc_1(A_510, B_511))) | ~v1_funct_1(C_512))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.71/3.50  tff(c_4689, plain, (![D_513]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_513)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_76, c_4684])).
% 9.71/3.50  tff(c_4697, plain, (![D_513]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_513)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4689])).
% 9.71/3.50  tff(c_4964, plain, (![D_513]: (v1_funct_1(k7_relat_1('#skF_5', D_513)))), inference(demodulation, [status(thm), theory('equality')], [c_4963, c_4697])).
% 9.71/3.50  tff(c_1460, plain, (![A_254, B_255, C_256]: (k1_relset_1(A_254, B_255, C_256)=k1_relat_1(C_256) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.71/3.50  tff(c_1475, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_1460])).
% 9.71/3.50  tff(c_5157, plain, (![B_581, A_582, C_583]: (k1_xboole_0=B_581 | k1_relset_1(A_582, B_581, C_583)=A_582 | ~v1_funct_2(C_583, A_582, B_581) | ~m1_subset_1(C_583, k1_zfmisc_1(k2_zfmisc_1(A_582, B_581))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.71/3.50  tff(c_5167, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_5157])).
% 9.71/3.50  tff(c_5178, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1475, c_5167])).
% 9.71/3.50  tff(c_5179, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_88, c_5178])).
% 9.71/3.50  tff(c_5194, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_5', A_17))=A_17 | ~r1_tarski(A_17, '#skF_2') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5179, c_32])).
% 9.71/3.50  tff(c_5269, plain, (![A_586]: (k1_relat_1(k7_relat_1('#skF_5', A_586))=A_586 | ~r1_tarski(A_586, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_5194])).
% 9.71/3.50  tff(c_64, plain, (![B_43, A_42]: (m1_subset_1(B_43, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_43), A_42))) | ~r1_tarski(k2_relat_1(B_43), A_42) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.71/3.50  tff(c_5278, plain, (![A_586, A_42]: (m1_subset_1(k7_relat_1('#skF_5', A_586), k1_zfmisc_1(k2_zfmisc_1(A_586, A_42))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', A_586)), A_42) | ~v1_funct_1(k7_relat_1('#skF_5', A_586)) | ~v1_relat_1(k7_relat_1('#skF_5', A_586)) | ~r1_tarski(A_586, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5269, c_64])).
% 9.71/3.50  tff(c_10410, plain, (![A_943, A_944]: (m1_subset_1(k7_relat_1('#skF_5', A_943), k1_zfmisc_1(k2_zfmisc_1(A_943, A_944))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', A_943)), A_944) | ~r1_tarski(A_943, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1183, c_4964, c_5278])).
% 9.71/3.50  tff(c_915, plain, (![A_168, B_169, C_170, D_171]: (v1_funct_1(k2_partfun1(A_168, B_169, C_170, D_171)) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))) | ~v1_funct_1(C_170))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.71/3.50  tff(c_920, plain, (![D_171]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_171)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_76, c_915])).
% 9.71/3.50  tff(c_928, plain, (![D_171]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_171)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_920])).
% 9.71/3.50  tff(c_70, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.71/3.50  tff(c_161, plain, (~v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_70])).
% 9.71/3.50  tff(c_931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_928, c_161])).
% 9.71/3.50  tff(c_932, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_70])).
% 9.71/3.50  tff(c_982, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_932])).
% 9.71/3.50  tff(c_4966, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4963, c_982])).
% 9.71/3.50  tff(c_10425, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_4')), '#skF_3') | ~r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_10410, c_4966])).
% 9.71/3.50  tff(c_10467, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_10425])).
% 9.71/3.50  tff(c_10486, plain, (~v5_relat_1(k7_relat_1('#skF_5', '#skF_4'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_10467])).
% 9.71/3.50  tff(c_10490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1183, c_5483, c_10486])).
% 9.71/3.50  tff(c_10492, plain, (m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_932])).
% 9.71/3.50  tff(c_11142, plain, (k1_relset_1('#skF_4', '#skF_3', k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))=k1_relat_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_10492, c_11125])).
% 9.71/3.50  tff(c_11750, plain, (k1_relset_1('#skF_4', '#skF_3', k7_relat_1('#skF_5', '#skF_4'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11747, c_11747, c_11142])).
% 9.71/3.50  tff(c_10491, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_932])).
% 9.71/3.50  tff(c_11757, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_4'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11747, c_10491])).
% 9.71/3.50  tff(c_11756, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_11747, c_10492])).
% 9.71/3.50  tff(c_11925, plain, (![B_1121, C_1122, A_1123]: (k1_xboole_0=B_1121 | v1_funct_2(C_1122, A_1123, B_1121) | k1_relset_1(A_1123, B_1121, C_1122)!=A_1123 | ~m1_subset_1(C_1122, k1_zfmisc_1(k2_zfmisc_1(A_1123, B_1121))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.71/3.50  tff(c_11928, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_4'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_11756, c_11925])).
% 9.71/3.50  tff(c_11947, plain, (k1_relset_1('#skF_4', '#skF_3', k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_11757, c_88, c_11928])).
% 9.71/3.50  tff(c_12035, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11750, c_11947])).
% 9.71/3.50  tff(c_12042, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11816, c_12035])).
% 9.71/3.50  tff(c_12046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_12042])).
% 9.71/3.50  tff(c_12048, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_72])).
% 9.71/3.50  tff(c_12047, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_72])).
% 9.71/3.50  tff(c_12054, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12048, c_12047])).
% 9.71/3.50  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.71/3.50  tff(c_12049, plain, (![A_8]: (r1_tarski('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_12047, c_14])).
% 9.71/3.50  tff(c_12065, plain, (![A_8]: (r1_tarski('#skF_3', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_12054, c_12049])).
% 9.71/3.50  tff(c_12060, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12054, c_74])).
% 9.71/3.50  tff(c_13589, plain, (![B_1337, A_1338]: (B_1337=A_1338 | ~r1_tarski(B_1337, A_1338) | ~r1_tarski(A_1338, B_1337))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.71/3.50  tff(c_13595, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_12060, c_13589])).
% 9.71/3.50  tff(c_13606, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12065, c_13595])).
% 9.71/3.50  tff(c_20, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.71/3.50  tff(c_12067, plain, (![B_10]: (k2_zfmisc_1('#skF_3', B_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12048, c_12048, c_20])).
% 9.71/3.50  tff(c_12091, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12067, c_12054, c_76])).
% 9.71/3.50  tff(c_12092, plain, (![A_1129, B_1130]: (r1_tarski(A_1129, B_1130) | ~m1_subset_1(A_1129, k1_zfmisc_1(B_1130)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.71/3.50  tff(c_12096, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_12091, c_12092])).
% 9.71/3.50  tff(c_13593, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_12096, c_13589])).
% 9.71/3.50  tff(c_13603, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12065, c_13593])).
% 9.71/3.50  tff(c_13640, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13606, c_13603])).
% 9.71/3.50  tff(c_12059, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12054, c_78])).
% 9.71/3.50  tff(c_13621, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13606, c_13606, c_12059])).
% 9.71/3.50  tff(c_13641, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13640, c_13621])).
% 9.71/3.50  tff(c_13618, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13606, c_12091])).
% 9.71/3.50  tff(c_13703, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13640, c_13618])).
% 9.71/3.50  tff(c_13620, plain, (![B_10]: (k2_zfmisc_1('#skF_4', B_10)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13606, c_13606, c_12067])).
% 9.71/3.50  tff(c_13901, plain, (![C_1376, B_1377, A_1378]: (v5_relat_1(C_1376, B_1377) | ~m1_subset_1(C_1376, k1_zfmisc_1(k2_zfmisc_1(A_1378, B_1377))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.71/3.50  tff(c_13931, plain, (![C_1384, B_1385]: (v5_relat_1(C_1384, B_1385) | ~m1_subset_1(C_1384, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_13620, c_13901])).
% 9.71/3.50  tff(c_13937, plain, (![B_1385]: (v5_relat_1('#skF_4', B_1385))), inference(resolution, [status(thm)], [c_13703, c_13931])).
% 9.71/3.50  tff(c_13643, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13640, c_80])).
% 9.71/3.50  tff(c_24, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.71/3.50  tff(c_18, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.71/3.50  tff(c_12075, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12048, c_12048, c_18])).
% 9.71/3.50  tff(c_12103, plain, (![C_1135, A_1136, B_1137]: (v1_relat_1(C_1135) | ~m1_subset_1(C_1135, k1_zfmisc_1(k2_zfmisc_1(A_1136, B_1137))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.71/3.50  tff(c_12114, plain, (![C_1140]: (v1_relat_1(C_1140) | ~m1_subset_1(C_1140, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_12075, c_12103])).
% 9.71/3.50  tff(c_12124, plain, (![A_1141]: (v1_relat_1(A_1141) | ~r1_tarski(A_1141, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_12114])).
% 9.71/3.50  tff(c_12146, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12060, c_12124])).
% 9.71/3.50  tff(c_30, plain, (![B_16, A_15]: (r1_tarski(k7_relat_1(B_16, A_15), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.71/3.50  tff(c_13607, plain, (![A_8]: (A_8='#skF_3' | ~r1_tarski(A_8, '#skF_3'))), inference(resolution, [status(thm)], [c_12065, c_13589])).
% 9.71/3.50  tff(c_13713, plain, (![A_1345]: (A_1345='#skF_4' | ~r1_tarski(A_1345, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13606, c_13606, c_13607])).
% 9.71/3.50  tff(c_13721, plain, (![A_15]: (k7_relat_1('#skF_4', A_15)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_13713])).
% 9.71/3.50  tff(c_13730, plain, (![A_15]: (k7_relat_1('#skF_4', A_15)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12146, c_13721])).
% 9.71/3.50  tff(c_14783, plain, (![A_1496, B_1497, C_1498, D_1499]: (k2_partfun1(A_1496, B_1497, C_1498, D_1499)=k7_relat_1(C_1498, D_1499) | ~m1_subset_1(C_1498, k1_zfmisc_1(k2_zfmisc_1(A_1496, B_1497))) | ~v1_funct_1(C_1498))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.71/3.50  tff(c_16473, plain, (![B_1639, C_1640, D_1641]: (k2_partfun1('#skF_4', B_1639, C_1640, D_1641)=k7_relat_1(C_1640, D_1641) | ~m1_subset_1(C_1640, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_1640))), inference(superposition, [status(thm), theory('equality')], [c_13620, c_14783])).
% 9.71/3.50  tff(c_16477, plain, (![B_1639, D_1641]: (k2_partfun1('#skF_4', B_1639, '#skF_4', D_1641)=k7_relat_1('#skF_4', D_1641) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_13703, c_16473])).
% 9.71/3.50  tff(c_16484, plain, (![B_1639, D_1641]: (k2_partfun1('#skF_4', B_1639, '#skF_4', D_1641)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13643, c_13730, c_16477])).
% 9.71/3.50  tff(c_14957, plain, (![A_1530, B_1531, C_1532, D_1533]: (m1_subset_1(k2_partfun1(A_1530, B_1531, C_1532, D_1533), k1_zfmisc_1(k2_zfmisc_1(A_1530, B_1531))) | ~m1_subset_1(C_1532, k1_zfmisc_1(k2_zfmisc_1(A_1530, B_1531))) | ~v1_funct_1(C_1532))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.71/3.50  tff(c_38, plain, (![C_24, A_22, B_23]: (v1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.71/3.50  tff(c_15711, plain, (![A_1572, B_1573, C_1574, D_1575]: (v1_relat_1(k2_partfun1(A_1572, B_1573, C_1574, D_1575)) | ~m1_subset_1(C_1574, k1_zfmisc_1(k2_zfmisc_1(A_1572, B_1573))) | ~v1_funct_1(C_1574))), inference(resolution, [status(thm)], [c_14957, c_38])).
% 9.71/3.50  tff(c_15726, plain, (![B_1576, C_1577, D_1578]: (v1_relat_1(k2_partfun1('#skF_4', B_1576, C_1577, D_1578)) | ~m1_subset_1(C_1577, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_1577))), inference(superposition, [status(thm), theory('equality')], [c_13620, c_15711])).
% 9.71/3.50  tff(c_15730, plain, (![B_1576, D_1578]: (v1_relat_1(k2_partfun1('#skF_4', B_1576, '#skF_4', D_1578)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_13703, c_15726])).
% 9.71/3.50  tff(c_15737, plain, (![B_1576, D_1578]: (v1_relat_1(k2_partfun1('#skF_4', B_1576, '#skF_4', D_1578)))), inference(demodulation, [status(thm), theory('equality')], [c_13643, c_15730])).
% 9.71/3.50  tff(c_13619, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13606, c_13606, c_12075])).
% 9.71/3.50  tff(c_14492, plain, (![A_1454, B_1455, C_1456, D_1457]: (v1_funct_1(k2_partfun1(A_1454, B_1455, C_1456, D_1457)) | ~m1_subset_1(C_1456, k1_zfmisc_1(k2_zfmisc_1(A_1454, B_1455))) | ~v1_funct_1(C_1456))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.71/3.50  tff(c_14915, plain, (![A_1514, C_1515, D_1516]: (v1_funct_1(k2_partfun1(A_1514, '#skF_4', C_1515, D_1516)) | ~m1_subset_1(C_1515, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_1515))), inference(superposition, [status(thm), theory('equality')], [c_13619, c_14492])).
% 9.71/3.50  tff(c_14917, plain, (![A_1514, D_1516]: (v1_funct_1(k2_partfun1(A_1514, '#skF_4', '#skF_4', D_1516)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_13703, c_14915])).
% 9.71/3.50  tff(c_14923, plain, (![A_1514, D_1516]: (v1_funct_1(k2_partfun1(A_1514, '#skF_4', '#skF_4', D_1516)))), inference(demodulation, [status(thm), theory('equality')], [c_13643, c_14917])).
% 9.71/3.50  tff(c_14652, plain, (![B_1480, A_1481]: (m1_subset_1(B_1480, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1480), A_1481))) | ~r1_tarski(k2_relat_1(B_1480), A_1481) | ~v1_funct_1(B_1480) | ~v1_relat_1(B_1480))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.71/3.50  tff(c_15001, plain, (![B_1537]: (m1_subset_1(B_1537, k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_relat_1(B_1537), '#skF_4') | ~v1_funct_1(B_1537) | ~v1_relat_1(B_1537))), inference(superposition, [status(thm), theory('equality')], [c_13619, c_14652])).
% 9.71/3.50  tff(c_15012, plain, (![B_1538]: (m1_subset_1(B_1538, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(B_1538) | ~v5_relat_1(B_1538, '#skF_4') | ~v1_relat_1(B_1538))), inference(resolution, [status(thm)], [c_28, c_15001])).
% 9.71/3.50  tff(c_12190, plain, (![B_1150, A_1151]: (B_1150=A_1151 | ~r1_tarski(B_1150, A_1151) | ~r1_tarski(A_1151, B_1150))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.71/3.50  tff(c_12196, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_12060, c_12190])).
% 9.71/3.50  tff(c_12207, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12065, c_12196])).
% 9.71/3.50  tff(c_12194, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_12096, c_12190])).
% 9.71/3.50  tff(c_12204, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12065, c_12194])).
% 9.71/3.50  tff(c_12241, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12207, c_12204])).
% 9.71/3.50  tff(c_12243, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12241, c_80])).
% 9.71/3.50  tff(c_12219, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12207, c_12091])).
% 9.71/3.50  tff(c_12281, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12241, c_12219])).
% 9.71/3.50  tff(c_12220, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12207, c_12207, c_12075])).
% 9.71/3.50  tff(c_13052, plain, (![A_1261, B_1262, C_1263, D_1264]: (v1_funct_1(k2_partfun1(A_1261, B_1262, C_1263, D_1264)) | ~m1_subset_1(C_1263, k1_zfmisc_1(k2_zfmisc_1(A_1261, B_1262))) | ~v1_funct_1(C_1263))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.71/3.50  tff(c_13524, plain, (![A_1325, C_1326, D_1327]: (v1_funct_1(k2_partfun1(A_1325, '#skF_4', C_1326, D_1327)) | ~m1_subset_1(C_1326, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_1326))), inference(superposition, [status(thm), theory('equality')], [c_12220, c_13052])).
% 9.71/3.50  tff(c_13526, plain, (![A_1325, D_1327]: (v1_funct_1(k2_partfun1(A_1325, '#skF_4', '#skF_4', D_1327)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_12281, c_13524])).
% 9.71/3.50  tff(c_13532, plain, (![A_1325, D_1327]: (v1_funct_1(k2_partfun1(A_1325, '#skF_4', '#skF_4', D_1327)))), inference(demodulation, [status(thm), theory('equality')], [c_12243, c_13526])).
% 9.71/3.50  tff(c_12149, plain, (~m1_subset_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1('#skF_3')) | ~v1_funct_2(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12054, c_12054, c_12075, c_12054, c_70])).
% 9.71/3.50  tff(c_12150, plain, (~v1_funct_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_12149])).
% 9.71/3.50  tff(c_12214, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12207, c_12207, c_12150])).
% 9.71/3.50  tff(c_12375, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12241, c_12214])).
% 9.71/3.50  tff(c_13554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13532, c_12375])).
% 9.71/3.50  tff(c_13555, plain, (~v1_funct_2(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_12149])).
% 9.71/3.50  tff(c_13709, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13640, c_13606, c_13606, c_13606, c_13640, c_13606, c_13606, c_13606, c_13555])).
% 9.71/3.50  tff(c_13710, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_13709])).
% 9.71/3.50  tff(c_15029, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')) | ~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4') | ~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_15012, c_13710])).
% 9.71/3.50  tff(c_15045, plain, (~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4') | ~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14923, c_15029])).
% 9.71/3.50  tff(c_15256, plain, (~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(splitLeft, [status(thm)], [c_15045])).
% 9.71/3.50  tff(c_15741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15737, c_15256])).
% 9.71/3.50  tff(c_15742, plain, (~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_15045])).
% 9.71/3.50  tff(c_16486, plain, (~v5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16484, c_15742])).
% 9.71/3.50  tff(c_16491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13937, c_16486])).
% 9.71/3.50  tff(c_16493, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_13709])).
% 9.71/3.50  tff(c_22, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.71/3.50  tff(c_16581, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_16493, c_22])).
% 9.71/3.50  tff(c_16495, plain, (![A_8]: (A_8='#skF_4' | ~r1_tarski(A_8, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13606, c_13606, c_13607])).
% 9.71/3.50  tff(c_16599, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_16581, c_16495])).
% 9.71/3.50  tff(c_16492, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_13709])).
% 9.71/3.50  tff(c_16616, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13641, c_16599, c_16492])).
% 9.71/3.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.71/3.50  
% 9.71/3.50  Inference rules
% 9.71/3.50  ----------------------
% 9.71/3.50  #Ref     : 0
% 9.71/3.50  #Sup     : 3481
% 9.71/3.50  #Fact    : 0
% 9.71/3.50  #Define  : 0
% 9.71/3.50  #Split   : 31
% 9.71/3.50  #Chain   : 0
% 9.71/3.50  #Close   : 0
% 9.71/3.50  
% 9.71/3.50  Ordering : KBO
% 9.71/3.50  
% 9.71/3.50  Simplification rules
% 9.71/3.50  ----------------------
% 9.71/3.50  #Subsume      : 401
% 9.71/3.50  #Demod        : 4967
% 9.71/3.50  #Tautology    : 1675
% 9.71/3.50  #SimpNegUnit  : 32
% 9.71/3.50  #BackRed      : 98
% 9.71/3.50  
% 9.71/3.50  #Partial instantiations: 0
% 9.71/3.50  #Strategies tried      : 1
% 9.71/3.50  
% 9.71/3.50  Timing (in seconds)
% 9.71/3.50  ----------------------
% 9.71/3.50  Preprocessing        : 0.35
% 9.71/3.50  Parsing              : 0.18
% 9.71/3.50  CNF conversion       : 0.02
% 9.71/3.50  Main loop            : 2.36
% 9.71/3.50  Inferencing          : 0.79
% 9.71/3.50  Reduction            : 0.89
% 9.71/3.50  Demodulation         : 0.67
% 9.71/3.50  BG Simplification    : 0.07
% 9.71/3.50  Subsumption          : 0.44
% 9.71/3.50  Abstraction          : 0.08
% 9.71/3.50  MUC search           : 0.00
% 9.71/3.50  Cooper               : 0.00
% 9.71/3.50  Total                : 2.77
% 9.71/3.50  Index Insertion      : 0.00
% 9.71/3.50  Index Deletion       : 0.00
% 9.71/3.50  Index Matching       : 0.00
% 9.71/3.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
