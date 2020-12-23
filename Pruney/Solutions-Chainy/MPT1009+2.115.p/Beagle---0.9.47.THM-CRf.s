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
% DateTime   : Thu Dec  3 10:14:58 EST 2020

% Result     : Theorem 21.72s
% Output     : CNFRefutation 21.78s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 561 expanded)
%              Number of leaves         :   42 ( 216 expanded)
%              Depth                    :   14
%              Number of atoms          :  201 (1382 expanded)
%              Number of equality atoms :   89 ( 601 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_95,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_139,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_117,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_70,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_127,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_52,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_204,plain,(
    ! [B_65,A_66] :
      ( v1_relat_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_207,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_204])).

tff(c_213,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_207])).

tff(c_54,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k9_relat_1(B_25,A_24),k2_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36234,plain,(
    ! [A_784,B_785,C_786,D_787] :
      ( k7_relset_1(A_784,B_785,C_786,D_787) = k9_relat_1(C_786,D_787)
      | ~ m1_subset_1(C_786,k1_zfmisc_1(k2_zfmisc_1(A_784,B_785))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_36247,plain,(
    ! [D_787] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_787) = k9_relat_1('#skF_4',D_787) ),
    inference(resolution,[status(thm)],[c_74,c_36234])).

tff(c_36306,plain,(
    ! [B_789,A_790] :
      ( k1_tarski(k1_funct_1(B_789,A_790)) = k2_relat_1(B_789)
      | k1_tarski(A_790) != k1_relat_1(B_789)
      | ~ v1_funct_1(B_789)
      | ~ v1_relat_1(B_789) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_70,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_36315,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36306,c_70])).

tff(c_36333,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_78,c_36315])).

tff(c_36375,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36247,c_36333])).

tff(c_36376,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_36375])).

tff(c_406,plain,(
    ! [C_103,A_104,B_105] :
      ( v4_relat_1(C_103,A_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_420,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_74,c_406])).

tff(c_46,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36396,plain,(
    ! [A_804,B_805,C_806,D_807] :
      ( k1_enumset1(A_804,B_805,C_806) = D_807
      | k2_tarski(A_804,C_806) = D_807
      | k2_tarski(B_805,C_806) = D_807
      | k2_tarski(A_804,B_805) = D_807
      | k1_tarski(C_806) = D_807
      | k1_tarski(B_805) = D_807
      | k1_tarski(A_804) = D_807
      | k1_xboole_0 = D_807
      | ~ r1_tarski(D_807,k1_enumset1(A_804,B_805,C_806)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36422,plain,(
    ! [A_5,B_6,D_807] :
      ( k1_enumset1(A_5,A_5,B_6) = D_807
      | k2_tarski(A_5,B_6) = D_807
      | k2_tarski(A_5,B_6) = D_807
      | k2_tarski(A_5,A_5) = D_807
      | k1_tarski(B_6) = D_807
      | k1_tarski(A_5) = D_807
      | k1_tarski(A_5) = D_807
      | k1_xboole_0 = D_807
      | ~ r1_tarski(D_807,k2_tarski(A_5,B_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_36396])).

tff(c_41313,plain,(
    ! [A_1046,B_1047,D_1048] :
      ( k2_tarski(A_1046,B_1047) = D_1048
      | k2_tarski(A_1046,B_1047) = D_1048
      | k2_tarski(A_1046,B_1047) = D_1048
      | k1_tarski(A_1046) = D_1048
      | k1_tarski(B_1047) = D_1048
      | k1_tarski(A_1046) = D_1048
      | k1_tarski(A_1046) = D_1048
      | k1_xboole_0 = D_1048
      | ~ r1_tarski(D_1048,k2_tarski(A_1046,B_1047)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_36422])).

tff(c_41330,plain,(
    ! [A_4,D_1048] :
      ( k2_tarski(A_4,A_4) = D_1048
      | k2_tarski(A_4,A_4) = D_1048
      | k2_tarski(A_4,A_4) = D_1048
      | k1_tarski(A_4) = D_1048
      | k1_tarski(A_4) = D_1048
      | k1_tarski(A_4) = D_1048
      | k1_tarski(A_4) = D_1048
      | k1_xboole_0 = D_1048
      | ~ r1_tarski(D_1048,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_41313])).

tff(c_66386,plain,(
    ! [A_1361,D_1362] :
      ( k1_tarski(A_1361) = D_1362
      | k1_tarski(A_1361) = D_1362
      | k1_tarski(A_1361) = D_1362
      | k1_tarski(A_1361) = D_1362
      | k1_tarski(A_1361) = D_1362
      | k1_tarski(A_1361) = D_1362
      | k1_tarski(A_1361) = D_1362
      | k1_xboole_0 = D_1362
      | ~ r1_tarski(D_1362,k1_tarski(A_1361)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_10,c_41330])).

tff(c_66571,plain,(
    ! [A_1365,B_1366] :
      ( k1_tarski(A_1365) = k1_relat_1(B_1366)
      | k1_relat_1(B_1366) = k1_xboole_0
      | ~ v4_relat_1(B_1366,k1_tarski(A_1365))
      | ~ v1_relat_1(B_1366) ) ),
    inference(resolution,[status(thm)],[c_46,c_66386])).

tff(c_66677,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_420,c_66571])).

tff(c_66717,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_66677])).

tff(c_66718,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_36376,c_66717])).

tff(c_36167,plain,(
    ! [A_779] :
      ( m1_subset_1(A_779,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_779),k2_relat_1(A_779))))
      | ~ v1_funct_1(A_779)
      | ~ v1_relat_1(A_779) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36519,plain,(
    ! [A_816] :
      ( r1_tarski(A_816,k2_zfmisc_1(k1_relat_1(A_816),k2_relat_1(A_816)))
      | ~ v1_funct_1(A_816)
      | ~ v1_relat_1(A_816) ) ),
    inference(resolution,[status(thm)],[c_36167,c_38])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36552,plain,(
    ! [A_816] :
      ( k2_zfmisc_1(k1_relat_1(A_816),k2_relat_1(A_816)) = A_816
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_816),k2_relat_1(A_816)),A_816)
      | ~ v1_funct_1(A_816)
      | ~ v1_relat_1(A_816) ) ),
    inference(resolution,[status(thm)],[c_36519,c_2])).

tff(c_66793,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_66718,c_36552])).

tff(c_67023,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_78,c_8,c_18,c_18,c_66718,c_66793])).

tff(c_67329,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67023,c_8])).

tff(c_85,plain,(
    ! [B_40] : k2_zfmisc_1(k1_xboole_0,B_40) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_89,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_52])).

tff(c_16,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_327,plain,(
    ! [C_86,B_87,A_88] :
      ( v5_relat_1(C_86,B_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_369,plain,(
    ! [A_97,B_98,A_99] :
      ( v5_relat_1(A_97,B_98)
      | ~ r1_tarski(A_97,k2_zfmisc_1(A_99,B_98)) ) ),
    inference(resolution,[status(thm)],[c_40,c_327])).

tff(c_394,plain,(
    ! [A_99,B_98] : v5_relat_1(k2_zfmisc_1(A_99,B_98),B_98) ),
    inference(resolution,[status(thm)],[c_6,c_369])).

tff(c_470,plain,(
    ! [B_119,A_120] :
      ( r1_tarski(k2_relat_1(B_119),A_120)
      | ~ v5_relat_1(B_119,A_120)
      | ~ v1_relat_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_163,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_190,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_163])).

tff(c_506,plain,(
    ! [B_123] :
      ( k2_relat_1(B_123) = k1_xboole_0
      | ~ v5_relat_1(B_123,k1_xboole_0)
      | ~ v1_relat_1(B_123) ) ),
    inference(resolution,[status(thm)],[c_470,c_190])).

tff(c_510,plain,(
    ! [A_99] :
      ( k2_relat_1(k2_zfmisc_1(A_99,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(A_99,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_394,c_506])).

tff(c_521,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_16,c_510])).

tff(c_538,plain,(
    ! [A_24] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_24),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_54])).

tff(c_561,plain,(
    ! [A_126] : r1_tarski(k9_relat_1(k1_xboole_0,A_126),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_538])).

tff(c_573,plain,(
    ! [A_126] : k9_relat_1(k1_xboole_0,A_126) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_561,c_190])).

tff(c_67315,plain,(
    ! [A_126] : k9_relat_1('#skF_4',A_126) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67023,c_67023,c_573])).

tff(c_36360,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36247,c_70])).

tff(c_67964,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67315,c_36360])).

tff(c_67968,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67329,c_67964])).

tff(c_67969,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_36375])).

tff(c_68055,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_67969])).

tff(c_68059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_68055])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:35:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.72/11.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.72/11.57  
% 21.72/11.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.78/11.57  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 21.78/11.57  
% 21.78/11.57  %Foreground sorts:
% 21.78/11.57  
% 21.78/11.57  
% 21.78/11.57  %Background operators:
% 21.78/11.57  
% 21.78/11.57  
% 21.78/11.57  %Foreground operators:
% 21.78/11.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 21.78/11.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.78/11.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 21.78/11.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.78/11.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.78/11.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 21.78/11.57  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 21.78/11.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.78/11.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 21.78/11.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 21.78/11.57  tff('#skF_2', type, '#skF_2': $i).
% 21.78/11.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 21.78/11.57  tff('#skF_3', type, '#skF_3': $i).
% 21.78/11.57  tff('#skF_1', type, '#skF_1': $i).
% 21.78/11.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 21.78/11.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.78/11.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 21.78/11.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.78/11.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 21.78/11.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 21.78/11.57  tff('#skF_4', type, '#skF_4': $i).
% 21.78/11.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.78/11.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 21.78/11.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 21.78/11.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.78/11.57  
% 21.78/11.59  tff(f_95, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 21.78/11.59  tff(f_139, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 21.78/11.59  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 21.78/11.59  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 21.78/11.59  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 21.78/11.59  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 21.78/11.59  tff(f_117, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 21.78/11.59  tff(f_107, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 21.78/11.59  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 21.78/11.59  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 21.78/11.59  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 21.78/11.59  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 21.78/11.59  tff(f_70, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 21.78/11.59  tff(f_127, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 21.78/11.59  tff(f_74, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 21.78/11.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 21.78/11.59  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 21.78/11.59  tff(c_52, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.78/11.59  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 21.78/11.59  tff(c_204, plain, (![B_65, A_66]: (v1_relat_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_81])).
% 21.78/11.59  tff(c_207, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_204])).
% 21.78/11.59  tff(c_213, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_207])).
% 21.78/11.59  tff(c_54, plain, (![B_25, A_24]: (r1_tarski(k9_relat_1(B_25, A_24), k2_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_99])).
% 21.78/11.59  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 21.78/11.59  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 21.78/11.59  tff(c_18, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 21.78/11.59  tff(c_36234, plain, (![A_784, B_785, C_786, D_787]: (k7_relset_1(A_784, B_785, C_786, D_787)=k9_relat_1(C_786, D_787) | ~m1_subset_1(C_786, k1_zfmisc_1(k2_zfmisc_1(A_784, B_785))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 21.78/11.59  tff(c_36247, plain, (![D_787]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_787)=k9_relat_1('#skF_4', D_787))), inference(resolution, [status(thm)], [c_74, c_36234])).
% 21.78/11.59  tff(c_36306, plain, (![B_789, A_790]: (k1_tarski(k1_funct_1(B_789, A_790))=k2_relat_1(B_789) | k1_tarski(A_790)!=k1_relat_1(B_789) | ~v1_funct_1(B_789) | ~v1_relat_1(B_789))), inference(cnfTransformation, [status(thm)], [f_107])).
% 21.78/11.59  tff(c_70, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 21.78/11.59  tff(c_36315, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36306, c_70])).
% 21.78/11.59  tff(c_36333, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_78, c_36315])).
% 21.78/11.59  tff(c_36375, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36247, c_36333])).
% 21.78/11.59  tff(c_36376, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_36375])).
% 21.78/11.59  tff(c_406, plain, (![C_103, A_104, B_105]: (v4_relat_1(C_103, A_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 21.78/11.59  tff(c_420, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_74, c_406])).
% 21.78/11.59  tff(c_46, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(B_19), A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_87])).
% 21.78/11.59  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 21.78/11.59  tff(c_12, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.78/11.59  tff(c_36396, plain, (![A_804, B_805, C_806, D_807]: (k1_enumset1(A_804, B_805, C_806)=D_807 | k2_tarski(A_804, C_806)=D_807 | k2_tarski(B_805, C_806)=D_807 | k2_tarski(A_804, B_805)=D_807 | k1_tarski(C_806)=D_807 | k1_tarski(B_805)=D_807 | k1_tarski(A_804)=D_807 | k1_xboole_0=D_807 | ~r1_tarski(D_807, k1_enumset1(A_804, B_805, C_806)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 21.78/11.59  tff(c_36422, plain, (![A_5, B_6, D_807]: (k1_enumset1(A_5, A_5, B_6)=D_807 | k2_tarski(A_5, B_6)=D_807 | k2_tarski(A_5, B_6)=D_807 | k2_tarski(A_5, A_5)=D_807 | k1_tarski(B_6)=D_807 | k1_tarski(A_5)=D_807 | k1_tarski(A_5)=D_807 | k1_xboole_0=D_807 | ~r1_tarski(D_807, k2_tarski(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_36396])).
% 21.78/11.59  tff(c_41313, plain, (![A_1046, B_1047, D_1048]: (k2_tarski(A_1046, B_1047)=D_1048 | k2_tarski(A_1046, B_1047)=D_1048 | k2_tarski(A_1046, B_1047)=D_1048 | k1_tarski(A_1046)=D_1048 | k1_tarski(B_1047)=D_1048 | k1_tarski(A_1046)=D_1048 | k1_tarski(A_1046)=D_1048 | k1_xboole_0=D_1048 | ~r1_tarski(D_1048, k2_tarski(A_1046, B_1047)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_36422])).
% 21.78/11.59  tff(c_41330, plain, (![A_4, D_1048]: (k2_tarski(A_4, A_4)=D_1048 | k2_tarski(A_4, A_4)=D_1048 | k2_tarski(A_4, A_4)=D_1048 | k1_tarski(A_4)=D_1048 | k1_tarski(A_4)=D_1048 | k1_tarski(A_4)=D_1048 | k1_tarski(A_4)=D_1048 | k1_xboole_0=D_1048 | ~r1_tarski(D_1048, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_41313])).
% 21.78/11.59  tff(c_66386, plain, (![A_1361, D_1362]: (k1_tarski(A_1361)=D_1362 | k1_tarski(A_1361)=D_1362 | k1_tarski(A_1361)=D_1362 | k1_tarski(A_1361)=D_1362 | k1_tarski(A_1361)=D_1362 | k1_tarski(A_1361)=D_1362 | k1_tarski(A_1361)=D_1362 | k1_xboole_0=D_1362 | ~r1_tarski(D_1362, k1_tarski(A_1361)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_10, c_41330])).
% 21.78/11.59  tff(c_66571, plain, (![A_1365, B_1366]: (k1_tarski(A_1365)=k1_relat_1(B_1366) | k1_relat_1(B_1366)=k1_xboole_0 | ~v4_relat_1(B_1366, k1_tarski(A_1365)) | ~v1_relat_1(B_1366))), inference(resolution, [status(thm)], [c_46, c_66386])).
% 21.78/11.59  tff(c_66677, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_420, c_66571])).
% 21.78/11.59  tff(c_66717, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_213, c_66677])).
% 21.78/11.59  tff(c_66718, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_36376, c_66717])).
% 21.78/11.59  tff(c_36167, plain, (![A_779]: (m1_subset_1(A_779, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_779), k2_relat_1(A_779)))) | ~v1_funct_1(A_779) | ~v1_relat_1(A_779))), inference(cnfTransformation, [status(thm)], [f_127])).
% 21.78/11.59  tff(c_38, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 21.78/11.59  tff(c_36519, plain, (![A_816]: (r1_tarski(A_816, k2_zfmisc_1(k1_relat_1(A_816), k2_relat_1(A_816))) | ~v1_funct_1(A_816) | ~v1_relat_1(A_816))), inference(resolution, [status(thm)], [c_36167, c_38])).
% 21.78/11.59  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.78/11.59  tff(c_36552, plain, (![A_816]: (k2_zfmisc_1(k1_relat_1(A_816), k2_relat_1(A_816))=A_816 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_816), k2_relat_1(A_816)), A_816) | ~v1_funct_1(A_816) | ~v1_relat_1(A_816))), inference(resolution, [status(thm)], [c_36519, c_2])).
% 21.78/11.59  tff(c_66793, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))='#skF_4' | ~r1_tarski(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4')), '#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_66718, c_36552])).
% 21.78/11.59  tff(c_67023, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_213, c_78, c_8, c_18, c_18, c_66718, c_66793])).
% 21.78/11.59  tff(c_67329, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_67023, c_8])).
% 21.78/11.59  tff(c_85, plain, (![B_40]: (k2_zfmisc_1(k1_xboole_0, B_40)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 21.78/11.59  tff(c_89, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_85, c_52])).
% 21.78/11.59  tff(c_16, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 21.78/11.59  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.78/11.59  tff(c_40, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_74])).
% 21.78/11.59  tff(c_327, plain, (![C_86, B_87, A_88]: (v5_relat_1(C_86, B_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 21.78/11.59  tff(c_369, plain, (![A_97, B_98, A_99]: (v5_relat_1(A_97, B_98) | ~r1_tarski(A_97, k2_zfmisc_1(A_99, B_98)))), inference(resolution, [status(thm)], [c_40, c_327])).
% 21.78/11.59  tff(c_394, plain, (![A_99, B_98]: (v5_relat_1(k2_zfmisc_1(A_99, B_98), B_98))), inference(resolution, [status(thm)], [c_6, c_369])).
% 21.78/11.59  tff(c_470, plain, (![B_119, A_120]: (r1_tarski(k2_relat_1(B_119), A_120) | ~v5_relat_1(B_119, A_120) | ~v1_relat_1(B_119))), inference(cnfTransformation, [status(thm)], [f_93])).
% 21.78/11.59  tff(c_163, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(B_62, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.78/11.59  tff(c_190, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_163])).
% 21.78/11.59  tff(c_506, plain, (![B_123]: (k2_relat_1(B_123)=k1_xboole_0 | ~v5_relat_1(B_123, k1_xboole_0) | ~v1_relat_1(B_123))), inference(resolution, [status(thm)], [c_470, c_190])).
% 21.78/11.59  tff(c_510, plain, (![A_99]: (k2_relat_1(k2_zfmisc_1(A_99, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(A_99, k1_xboole_0)))), inference(resolution, [status(thm)], [c_394, c_506])).
% 21.78/11.59  tff(c_521, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_16, c_510])).
% 21.78/11.59  tff(c_538, plain, (![A_24]: (r1_tarski(k9_relat_1(k1_xboole_0, A_24), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_521, c_54])).
% 21.78/11.59  tff(c_561, plain, (![A_126]: (r1_tarski(k9_relat_1(k1_xboole_0, A_126), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_538])).
% 21.78/11.59  tff(c_573, plain, (![A_126]: (k9_relat_1(k1_xboole_0, A_126)=k1_xboole_0)), inference(resolution, [status(thm)], [c_561, c_190])).
% 21.78/11.59  tff(c_67315, plain, (![A_126]: (k9_relat_1('#skF_4', A_126)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_67023, c_67023, c_573])).
% 21.78/11.59  tff(c_36360, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36247, c_70])).
% 21.78/11.59  tff(c_67964, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_67315, c_36360])).
% 21.78/11.59  tff(c_67968, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67329, c_67964])).
% 21.78/11.59  tff(c_67969, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_36375])).
% 21.78/11.59  tff(c_68055, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_67969])).
% 21.78/11.59  tff(c_68059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_213, c_68055])).
% 21.78/11.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.78/11.59  
% 21.78/11.59  Inference rules
% 21.78/11.59  ----------------------
% 21.78/11.59  #Ref     : 0
% 21.78/11.59  #Sup     : 15171
% 21.78/11.59  #Fact    : 0
% 21.78/11.59  #Define  : 0
% 21.78/11.59  #Split   : 26
% 21.78/11.59  #Chain   : 0
% 21.78/11.59  #Close   : 0
% 21.78/11.59  
% 21.78/11.59  Ordering : KBO
% 21.78/11.59  
% 21.78/11.59  Simplification rules
% 21.78/11.59  ----------------------
% 21.78/11.59  #Subsume      : 3925
% 21.78/11.59  #Demod        : 20915
% 21.78/11.59  #Tautology    : 5507
% 21.78/11.59  #SimpNegUnit  : 421
% 21.78/11.59  #BackRed      : 447
% 21.78/11.59  
% 21.78/11.59  #Partial instantiations: 0
% 21.78/11.59  #Strategies tried      : 1
% 21.78/11.59  
% 21.78/11.59  Timing (in seconds)
% 21.78/11.59  ----------------------
% 21.78/11.60  Preprocessing        : 0.34
% 21.78/11.60  Parsing              : 0.19
% 21.78/11.60  CNF conversion       : 0.02
% 21.78/11.60  Main loop            : 10.46
% 21.78/11.60  Inferencing          : 1.66
% 21.78/11.60  Reduction            : 3.85
% 21.78/11.60  Demodulation         : 3.09
% 21.78/11.60  BG Simplification    : 0.25
% 21.78/11.60  Subsumption          : 4.28
% 21.78/11.60  Abstraction          : 0.41
% 21.78/11.60  MUC search           : 0.00
% 21.78/11.60  Cooper               : 0.00
% 21.78/11.60  Total                : 10.84
% 21.78/11.60  Index Insertion      : 0.00
% 21.78/11.60  Index Deletion       : 0.00
% 21.78/11.60  Index Matching       : 0.00
% 21.78/11.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
