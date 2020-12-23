%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:35 EST 2020

% Result     : Theorem 4.77s
% Output     : CNFRefutation 4.94s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 621 expanded)
%              Number of leaves         :   44 ( 241 expanded)
%              Depth                    :   20
%              Number of atoms          :  186 (1504 expanded)
%              Number of equality atoms :   93 ( 737 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_146,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_124,axiom,(
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

tff(f_32,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_134,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_81,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_39,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_151,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_155,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_151])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_88,plain,(
    ! [A_37] :
      ( k1_xboole_0 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_92,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_88])).

tff(c_93,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2])).

tff(c_1799,plain,(
    ! [A_262,B_263,C_264] :
      ( k2_relset_1(A_262,B_263,C_264) = k2_relat_1(C_264)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_262,B_263))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1803,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1799])).

tff(c_70,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1804,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1803,c_70])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_76,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1790,plain,(
    ! [A_259,B_260,C_261] :
      ( k1_relset_1(A_259,B_260,C_261) = k1_relat_1(C_261)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1794,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1790])).

tff(c_1962,plain,(
    ! [B_280,A_281,C_282] :
      ( k1_xboole_0 = B_280
      | k1_relset_1(A_281,B_280,C_282) = A_281
      | ~ v1_funct_2(C_282,A_281,B_280)
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1(A_281,B_280))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1971,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_1962])).

tff(c_1979,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1794,c_1971])).

tff(c_1980,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1979])).

tff(c_6,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_116,plain,(
    ! [A_51,B_52] : k1_enumset1(A_51,A_51,B_52) = k2_tarski(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_28,plain,(
    ! [A_9,B_10,C_11] : r1_tarski(k1_tarski(A_9),k1_enumset1(A_9,B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_140,plain,(
    ! [A_56,B_57] : r1_tarski(k1_tarski(A_56),k2_tarski(A_56,B_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_28])).

tff(c_143,plain,(
    ! [A_2] : r1_tarski(k1_tarski(A_2),k1_tarski(A_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_140])).

tff(c_1996,plain,(
    r1_tarski(k1_relat_1('#skF_3'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1980,c_143])).

tff(c_2018,plain,(
    r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1980,c_1996])).

tff(c_32,plain,(
    ! [B_14,A_13] :
      ( v4_relat_1(B_14,A_13)
      | ~ r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2107,plain,
    ( v4_relat_1('#skF_3',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2018,c_32])).

tff(c_2110,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_2107])).

tff(c_36,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,A_15) = B_16
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2113,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2110,c_36])).

tff(c_2116,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_2113])).

tff(c_42,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_18,k1_tarski(A_17))),k1_tarski(k1_funct_1(B_18,A_17)))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2435,plain,(
    ! [B_318] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_318,k1_relat_1('#skF_3'))),k1_tarski(k1_funct_1(B_318,'#skF_1')))
      | ~ v1_funct_1(B_318)
      | ~ v1_relat_1(B_318) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1980,c_42])).

tff(c_2438,plain,
    ( r1_tarski(k2_relat_1('#skF_3'),k1_tarski(k1_funct_1('#skF_3','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2116,c_2435])).

tff(c_2443,plain,(
    r1_tarski(k2_relat_1('#skF_3'),k1_tarski(k1_funct_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_78,c_2438])).

tff(c_8,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2021,plain,(
    ! [A_283,B_284,C_285,D_286] :
      ( k1_enumset1(A_283,B_284,C_285) = D_286
      | k2_tarski(A_283,C_285) = D_286
      | k2_tarski(B_284,C_285) = D_286
      | k2_tarski(A_283,B_284) = D_286
      | k1_tarski(C_285) = D_286
      | k1_tarski(B_284) = D_286
      | k1_tarski(A_283) = D_286
      | k1_xboole_0 = D_286
      | ~ r1_tarski(D_286,k1_enumset1(A_283,B_284,C_285)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2040,plain,(
    ! [A_3,B_4,D_286] :
      ( k1_enumset1(A_3,A_3,B_4) = D_286
      | k2_tarski(A_3,B_4) = D_286
      | k2_tarski(A_3,B_4) = D_286
      | k2_tarski(A_3,A_3) = D_286
      | k1_tarski(B_4) = D_286
      | k1_tarski(A_3) = D_286
      | k1_tarski(A_3) = D_286
      | k1_xboole_0 = D_286
      | ~ r1_tarski(D_286,k2_tarski(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2021])).

tff(c_2216,plain,(
    ! [A_293,B_294,D_295] :
      ( k2_tarski(A_293,B_294) = D_295
      | k2_tarski(A_293,B_294) = D_295
      | k2_tarski(A_293,B_294) = D_295
      | k1_tarski(A_293) = D_295
      | k1_tarski(B_294) = D_295
      | k1_tarski(A_293) = D_295
      | k1_tarski(A_293) = D_295
      | k1_xboole_0 = D_295
      | ~ r1_tarski(D_295,k2_tarski(A_293,B_294)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8,c_2040])).

tff(c_2241,plain,(
    ! [A_2,D_295] :
      ( k2_tarski(A_2,A_2) = D_295
      | k2_tarski(A_2,A_2) = D_295
      | k2_tarski(A_2,A_2) = D_295
      | k1_tarski(A_2) = D_295
      | k1_tarski(A_2) = D_295
      | k1_tarski(A_2) = D_295
      | k1_tarski(A_2) = D_295
      | k1_xboole_0 = D_295
      | ~ r1_tarski(D_295,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2216])).

tff(c_2497,plain,(
    ! [A_325,D_326] :
      ( k1_tarski(A_325) = D_326
      | k1_tarski(A_325) = D_326
      | k1_tarski(A_325) = D_326
      | k1_tarski(A_325) = D_326
      | k1_tarski(A_325) = D_326
      | k1_tarski(A_325) = D_326
      | k1_tarski(A_325) = D_326
      | k1_xboole_0 = D_326
      | ~ r1_tarski(D_326,k1_tarski(A_325)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_6,c_2241])).

tff(c_2500,plain,
    ( k1_tarski(k1_funct_1('#skF_3','#skF_1')) = k2_relat_1('#skF_3')
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2443,c_2497])).

tff(c_2522,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1804,c_1804,c_1804,c_1804,c_1804,c_1804,c_1804,c_2500])).

tff(c_1809,plain,(
    ! [A_265] :
      ( m1_subset_1(A_265,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_265),k2_relat_1(A_265))))
      | ~ v1_funct_1(A_265)
      | ~ v1_relat_1(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_46,plain,(
    ! [C_25,B_23,A_22] :
      ( v1_xboole_0(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(B_23,A_22)))
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1830,plain,(
    ! [A_265] :
      ( v1_xboole_0(A_265)
      | ~ v1_xboole_0(k2_relat_1(A_265))
      | ~ v1_funct_1(A_265)
      | ~ v1_relat_1(A_265) ) ),
    inference(resolution,[status(thm)],[c_1809,c_46])).

tff(c_2544,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2522,c_1830])).

tff(c_2558,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_78,c_93,c_2544])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2567,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2558,c_4])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2603,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2567,c_2567,c_40])).

tff(c_12,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_tarski(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2015,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1980,c_12])).

tff(c_2629,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2603,c_2015])).

tff(c_2633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2629])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.77/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.77/1.97  
% 4.77/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.77/1.97  %$ v1_funct_2 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.77/1.97  
% 4.77/1.97  %Foreground sorts:
% 4.77/1.97  
% 4.77/1.97  
% 4.77/1.97  %Background operators:
% 4.77/1.97  
% 4.77/1.97  
% 4.77/1.97  %Foreground operators:
% 4.77/1.97  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.77/1.97  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 4.77/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.77/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.77/1.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.77/1.97  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.77/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.77/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.77/1.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.77/1.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.77/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.77/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.77/1.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.77/1.97  tff('#skF_2', type, '#skF_2': $i).
% 4.77/1.97  tff('#skF_3', type, '#skF_3': $i).
% 4.77/1.97  tff('#skF_1', type, '#skF_1': $i).
% 4.77/1.97  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.77/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.77/1.97  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.77/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.77/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.77/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.77/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.77/1.97  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.77/1.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.77/1.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.77/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.77/1.97  
% 4.94/1.99  tff(f_146, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 4.94/1.99  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.94/1.99  tff(f_26, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 4.94/1.99  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.94/1.99  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.94/1.99  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.94/1.99  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.94/1.99  tff(f_32, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.94/1.99  tff(f_34, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.94/1.99  tff(f_66, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 4.94/1.99  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.94/1.99  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 4.94/1.99  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 4.94/1.99  tff(f_134, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.94/1.99  tff(f_98, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.94/1.99  tff(f_81, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.94/1.99  tff(f_39, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 4.94/1.99  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.94/1.99  tff(c_151, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.94/1.99  tff(c_155, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_151])).
% 4.94/1.99  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.94/1.99  tff(c_2, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.94/1.99  tff(c_88, plain, (![A_37]: (k1_xboole_0=A_37 | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.94/1.99  tff(c_92, plain, (o_0_0_xboole_0=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_88])).
% 4.94/1.99  tff(c_93, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_2])).
% 4.94/1.99  tff(c_1799, plain, (![A_262, B_263, C_264]: (k2_relset_1(A_262, B_263, C_264)=k2_relat_1(C_264) | ~m1_subset_1(C_264, k1_zfmisc_1(k2_zfmisc_1(A_262, B_263))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.94/1.99  tff(c_1803, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1799])).
% 4.94/1.99  tff(c_70, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.94/1.99  tff(c_1804, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1803, c_70])).
% 4.94/1.99  tff(c_72, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.94/1.99  tff(c_76, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.94/1.99  tff(c_1790, plain, (![A_259, B_260, C_261]: (k1_relset_1(A_259, B_260, C_261)=k1_relat_1(C_261) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_259, B_260))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.94/1.99  tff(c_1794, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1790])).
% 4.94/1.99  tff(c_1962, plain, (![B_280, A_281, C_282]: (k1_xboole_0=B_280 | k1_relset_1(A_281, B_280, C_282)=A_281 | ~v1_funct_2(C_282, A_281, B_280) | ~m1_subset_1(C_282, k1_zfmisc_1(k2_zfmisc_1(A_281, B_280))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.94/1.99  tff(c_1971, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_74, c_1962])).
% 4.94/1.99  tff(c_1979, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1794, c_1971])).
% 4.94/1.99  tff(c_1980, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_72, c_1979])).
% 4.94/1.99  tff(c_6, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.94/1.99  tff(c_116, plain, (![A_51, B_52]: (k1_enumset1(A_51, A_51, B_52)=k2_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.94/1.99  tff(c_28, plain, (![A_9, B_10, C_11]: (r1_tarski(k1_tarski(A_9), k1_enumset1(A_9, B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.94/1.99  tff(c_140, plain, (![A_56, B_57]: (r1_tarski(k1_tarski(A_56), k2_tarski(A_56, B_57)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_28])).
% 4.94/1.99  tff(c_143, plain, (![A_2]: (r1_tarski(k1_tarski(A_2), k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_140])).
% 4.94/1.99  tff(c_1996, plain, (r1_tarski(k1_relat_1('#skF_3'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1980, c_143])).
% 4.94/1.99  tff(c_2018, plain, (r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1980, c_1996])).
% 4.94/1.99  tff(c_32, plain, (![B_14, A_13]: (v4_relat_1(B_14, A_13) | ~r1_tarski(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.94/1.99  tff(c_2107, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2018, c_32])).
% 4.94/1.99  tff(c_2110, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_2107])).
% 4.94/1.99  tff(c_36, plain, (![B_16, A_15]: (k7_relat_1(B_16, A_15)=B_16 | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.94/1.99  tff(c_2113, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2110, c_36])).
% 4.94/1.99  tff(c_2116, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_2113])).
% 4.94/1.99  tff(c_42, plain, (![B_18, A_17]: (r1_tarski(k2_relat_1(k7_relat_1(B_18, k1_tarski(A_17))), k1_tarski(k1_funct_1(B_18, A_17))) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.94/1.99  tff(c_2435, plain, (![B_318]: (r1_tarski(k2_relat_1(k7_relat_1(B_318, k1_relat_1('#skF_3'))), k1_tarski(k1_funct_1(B_318, '#skF_1'))) | ~v1_funct_1(B_318) | ~v1_relat_1(B_318))), inference(superposition, [status(thm), theory('equality')], [c_1980, c_42])).
% 4.94/1.99  tff(c_2438, plain, (r1_tarski(k2_relat_1('#skF_3'), k1_tarski(k1_funct_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2116, c_2435])).
% 4.94/1.99  tff(c_2443, plain, (r1_tarski(k2_relat_1('#skF_3'), k1_tarski(k1_funct_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_78, c_2438])).
% 4.94/1.99  tff(c_8, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.94/1.99  tff(c_2021, plain, (![A_283, B_284, C_285, D_286]: (k1_enumset1(A_283, B_284, C_285)=D_286 | k2_tarski(A_283, C_285)=D_286 | k2_tarski(B_284, C_285)=D_286 | k2_tarski(A_283, B_284)=D_286 | k1_tarski(C_285)=D_286 | k1_tarski(B_284)=D_286 | k1_tarski(A_283)=D_286 | k1_xboole_0=D_286 | ~r1_tarski(D_286, k1_enumset1(A_283, B_284, C_285)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.94/1.99  tff(c_2040, plain, (![A_3, B_4, D_286]: (k1_enumset1(A_3, A_3, B_4)=D_286 | k2_tarski(A_3, B_4)=D_286 | k2_tarski(A_3, B_4)=D_286 | k2_tarski(A_3, A_3)=D_286 | k1_tarski(B_4)=D_286 | k1_tarski(A_3)=D_286 | k1_tarski(A_3)=D_286 | k1_xboole_0=D_286 | ~r1_tarski(D_286, k2_tarski(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2021])).
% 4.94/1.99  tff(c_2216, plain, (![A_293, B_294, D_295]: (k2_tarski(A_293, B_294)=D_295 | k2_tarski(A_293, B_294)=D_295 | k2_tarski(A_293, B_294)=D_295 | k1_tarski(A_293)=D_295 | k1_tarski(B_294)=D_295 | k1_tarski(A_293)=D_295 | k1_tarski(A_293)=D_295 | k1_xboole_0=D_295 | ~r1_tarski(D_295, k2_tarski(A_293, B_294)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8, c_2040])).
% 4.94/1.99  tff(c_2241, plain, (![A_2, D_295]: (k2_tarski(A_2, A_2)=D_295 | k2_tarski(A_2, A_2)=D_295 | k2_tarski(A_2, A_2)=D_295 | k1_tarski(A_2)=D_295 | k1_tarski(A_2)=D_295 | k1_tarski(A_2)=D_295 | k1_tarski(A_2)=D_295 | k1_xboole_0=D_295 | ~r1_tarski(D_295, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2216])).
% 4.94/1.99  tff(c_2497, plain, (![A_325, D_326]: (k1_tarski(A_325)=D_326 | k1_tarski(A_325)=D_326 | k1_tarski(A_325)=D_326 | k1_tarski(A_325)=D_326 | k1_tarski(A_325)=D_326 | k1_tarski(A_325)=D_326 | k1_tarski(A_325)=D_326 | k1_xboole_0=D_326 | ~r1_tarski(D_326, k1_tarski(A_325)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_6, c_2241])).
% 4.94/1.99  tff(c_2500, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))=k2_relat_1('#skF_3') | k2_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_2443, c_2497])).
% 4.94/1.99  tff(c_2522, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1804, c_1804, c_1804, c_1804, c_1804, c_1804, c_1804, c_2500])).
% 4.94/1.99  tff(c_1809, plain, (![A_265]: (m1_subset_1(A_265, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_265), k2_relat_1(A_265)))) | ~v1_funct_1(A_265) | ~v1_relat_1(A_265))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.94/1.99  tff(c_46, plain, (![C_25, B_23, A_22]: (v1_xboole_0(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(B_23, A_22))) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.94/1.99  tff(c_1830, plain, (![A_265]: (v1_xboole_0(A_265) | ~v1_xboole_0(k2_relat_1(A_265)) | ~v1_funct_1(A_265) | ~v1_relat_1(A_265))), inference(resolution, [status(thm)], [c_1809, c_46])).
% 4.94/1.99  tff(c_2544, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_xboole_0) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2522, c_1830])).
% 4.94/1.99  tff(c_2558, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_78, c_93, c_2544])).
% 4.94/1.99  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.94/1.99  tff(c_2567, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2558, c_4])).
% 4.94/1.99  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.94/1.99  tff(c_2603, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2567, c_2567, c_40])).
% 4.94/1.99  tff(c_12, plain, (![A_8]: (~v1_xboole_0(k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.94/1.99  tff(c_2015, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1980, c_12])).
% 4.94/1.99  tff(c_2629, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2603, c_2015])).
% 4.94/1.99  tff(c_2633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2629])).
% 4.94/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.94/1.99  
% 4.94/1.99  Inference rules
% 4.94/1.99  ----------------------
% 4.94/1.99  #Ref     : 0
% 4.94/1.99  #Sup     : 522
% 4.94/1.99  #Fact    : 0
% 4.94/1.99  #Define  : 0
% 4.94/1.99  #Split   : 5
% 4.94/1.99  #Chain   : 0
% 4.94/1.99  #Close   : 0
% 4.94/1.99  
% 4.94/1.99  Ordering : KBO
% 4.94/1.99  
% 4.94/1.99  Simplification rules
% 4.94/1.99  ----------------------
% 4.94/1.99  #Subsume      : 35
% 4.94/1.99  #Demod        : 673
% 4.94/1.99  #Tautology    : 342
% 4.94/1.99  #SimpNegUnit  : 15
% 4.94/1.99  #BackRed      : 134
% 4.94/1.99  
% 4.94/1.99  #Partial instantiations: 0
% 4.94/1.99  #Strategies tried      : 1
% 4.94/1.99  
% 4.94/1.99  Timing (in seconds)
% 4.94/1.99  ----------------------
% 4.94/2.00  Preprocessing        : 0.35
% 4.94/2.00  Parsing              : 0.19
% 4.94/2.00  CNF conversion       : 0.02
% 4.94/2.00  Main loop            : 0.79
% 4.94/2.00  Inferencing          : 0.28
% 4.94/2.00  Reduction            : 0.29
% 4.94/2.00  Demodulation         : 0.22
% 4.94/2.00  BG Simplification    : 0.03
% 4.94/2.00  Subsumption          : 0.12
% 4.94/2.00  Abstraction          : 0.04
% 4.94/2.00  MUC search           : 0.00
% 4.94/2.00  Cooper               : 0.00
% 4.94/2.00  Total                : 1.19
% 4.94/2.00  Index Insertion      : 0.00
% 4.94/2.00  Index Deletion       : 0.00
% 4.94/2.00  Index Matching       : 0.00
% 4.94/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
