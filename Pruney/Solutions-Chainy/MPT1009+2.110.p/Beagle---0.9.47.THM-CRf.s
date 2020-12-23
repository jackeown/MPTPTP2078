%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:57 EST 2020

% Result     : Theorem 17.17s
% Output     : CNFRefutation 17.34s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 551 expanded)
%              Number of leaves         :   49 ( 206 expanded)
%              Depth                    :   11
%              Number of atoms          :  193 (1156 expanded)
%              Number of equality atoms :   57 ( 263 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_91,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_147,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_135,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_125,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

tff(c_62,plain,(
    ! [A_32,B_33] : v1_relat_1(k2_zfmisc_1(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_88,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_170,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_173,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_88,c_170])).

tff(c_182,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_173])).

tff(c_92,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_42,plain,(
    ! [B_18] : k2_zfmisc_1(k1_xboole_0,B_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_445,plain,(
    ! [C_121,A_122,B_123] :
      ( v4_relat_1(C_121,A_122)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_463,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_88,c_445])).

tff(c_56,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k1_relat_1(B_29),A_28)
      | ~ v4_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_271,plain,(
    ! [B_88,A_89] :
      ( k1_tarski(B_88) = A_89
      | k1_xboole_0 = A_89
      | ~ r1_tarski(A_89,k1_tarski(B_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_35008,plain,(
    ! [B_65083,B_65084] :
      ( k1_tarski(B_65083) = k1_relat_1(B_65084)
      | k1_relat_1(B_65084) = k1_xboole_0
      | ~ v4_relat_1(B_65084,k1_tarski(B_65083))
      | ~ v1_relat_1(B_65084) ) ),
    inference(resolution,[status(thm)],[c_56,c_271])).

tff(c_35068,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_463,c_35008])).

tff(c_35085,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_35068])).

tff(c_35089,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_35085])).

tff(c_29816,plain,(
    ! [A_47936] :
      ( m1_subset_1(A_47936,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_47936),k2_relat_1(A_47936))))
      | ~ v1_funct_1(A_47936)
      | ~ v1_relat_1(A_47936) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_29846,plain,(
    ! [A_47936] :
      ( r1_tarski(A_47936,k2_zfmisc_1(k1_relat_1(A_47936),k2_relat_1(A_47936)))
      | ~ v1_funct_1(A_47936)
      | ~ v1_relat_1(A_47936) ) ),
    inference(resolution,[status(thm)],[c_29816,c_46])).

tff(c_35123,plain,
    ( r1_tarski('#skF_6',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_6')))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_35089,c_29846])).

tff(c_35171,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_92,c_42,c_35123])).

tff(c_44,plain,(
    ! [A_19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_146,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,B_67)
      | ~ m1_subset_1(A_66,k1_zfmisc_1(B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_154,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(resolution,[status(thm)],[c_44,c_146])).

tff(c_202,plain,(
    ! [B_75,A_76] :
      ( B_75 = A_76
      | ~ r1_tarski(B_75,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_210,plain,(
    ! [A_19] :
      ( k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_154,c_202])).

tff(c_35225,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_35171,c_210])).

tff(c_35284,plain,(
    ! [A_19] : r1_tarski('#skF_6',A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35225,c_154])).

tff(c_40,plain,(
    ! [A_17] : k2_zfmisc_1(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_289,plain,(
    ! [C_90,B_91,A_92] :
      ( v5_relat_1(C_90,B_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_92,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_343,plain,(
    ! [A_105,B_106,A_107] :
      ( v5_relat_1(A_105,B_106)
      | ~ r1_tarski(A_105,k2_zfmisc_1(A_107,B_106)) ) ),
    inference(resolution,[status(thm)],[c_48,c_289])).

tff(c_370,plain,(
    ! [A_107,B_106] : v5_relat_1(k2_zfmisc_1(A_107,B_106),B_106) ),
    inference(resolution,[status(thm)],[c_6,c_343])).

tff(c_504,plain,(
    ! [B_125,A_126] :
      ( r1_tarski(k2_relat_1(B_125),A_126)
      | ~ v5_relat_1(B_125,A_126)
      | ~ v1_relat_1(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_684,plain,(
    ! [B_144] :
      ( k2_relat_1(B_144) = k1_xboole_0
      | ~ v5_relat_1(B_144,k1_xboole_0)
      | ~ v1_relat_1(B_144) ) ),
    inference(resolution,[status(thm)],[c_504,c_210])).

tff(c_688,plain,(
    ! [A_107] :
      ( k2_relat_1(k2_zfmisc_1(A_107,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(A_107,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_370,c_684])).

tff(c_699,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_40,c_688])).

tff(c_98,plain,(
    ! [B_55] : k2_zfmisc_1(k1_xboole_0,B_55) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_102,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_62])).

tff(c_466,plain,(
    ! [A_124] : v4_relat_1(k1_xboole_0,A_124) ),
    inference(resolution,[status(thm)],[c_44,c_445])).

tff(c_68,plain,(
    ! [B_39,A_38] :
      ( k7_relat_1(B_39,A_38) = B_39
      | ~ v4_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_469,plain,(
    ! [A_124] :
      ( k7_relat_1(k1_xboole_0,A_124) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_466,c_68])).

tff(c_540,plain,(
    ! [A_127] : k7_relat_1(k1_xboole_0,A_127) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_469])).

tff(c_66,plain,(
    ! [B_37,A_36] :
      ( k2_relat_1(k7_relat_1(B_37,A_36)) = k9_relat_1(B_37,A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_549,plain,(
    ! [A_127] :
      ( k9_relat_1(k1_xboole_0,A_127) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_66])).

tff(c_561,plain,(
    ! [A_127] : k9_relat_1(k1_xboole_0,A_127) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_549])).

tff(c_704,plain,(
    ! [A_127] : k9_relat_1(k1_xboole_0,A_127) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_561])).

tff(c_35268,plain,(
    ! [A_127] : k9_relat_1('#skF_6',A_127) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35225,c_35225,c_704])).

tff(c_29935,plain,(
    ! [A_47944,B_47945,C_47946,D_47947] :
      ( k7_relset_1(A_47944,B_47945,C_47946,D_47947) = k9_relat_1(C_47946,D_47947)
      | ~ m1_subset_1(C_47946,k1_zfmisc_1(k2_zfmisc_1(A_47944,B_47945))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_29951,plain,(
    ! [D_47947] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_47947) = k9_relat_1('#skF_6',D_47947) ),
    inference(resolution,[status(thm)],[c_88,c_29935])).

tff(c_84,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_29969,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29951,c_84])).

tff(c_35801,plain,(
    ~ r1_tarski('#skF_6',k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35268,c_29969])).

tff(c_35805,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35284,c_35801])).

tff(c_35806,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_35085])).

tff(c_536,plain,
    ( k7_relat_1('#skF_6',k1_tarski('#skF_3')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_463,c_68])).

tff(c_539,plain,(
    k7_relat_1('#skF_6',k1_tarski('#skF_3')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_536])).

tff(c_35812,plain,(
    k7_relat_1('#skF_6',k1_relat_1('#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35806,c_539])).

tff(c_35921,plain,
    ( k9_relat_1('#skF_6',k1_relat_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_35812,c_66])).

tff(c_35934,plain,(
    k9_relat_1('#skF_6',k1_relat_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_35921])).

tff(c_410,plain,(
    ! [B_117,A_118] :
      ( k2_relat_1(k7_relat_1(B_117,A_118)) = k9_relat_1(B_117,A_118)
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_64,plain,(
    ! [B_35,A_34] :
      ( r1_tarski(k9_relat_1(B_35,A_34),k2_relat_1(B_35))
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_37312,plain,(
    ! [B_70239,A_70240,A_70241] :
      ( r1_tarski(k9_relat_1(k7_relat_1(B_70239,A_70240),A_70241),k9_relat_1(B_70239,A_70240))
      | ~ v1_relat_1(k7_relat_1(B_70239,A_70240))
      | ~ v1_relat_1(B_70239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_64])).

tff(c_37330,plain,(
    ! [A_70241] :
      ( r1_tarski(k9_relat_1('#skF_6',A_70241),k9_relat_1('#skF_6',k1_relat_1('#skF_6')))
      | ~ v1_relat_1(k7_relat_1('#skF_6',k1_relat_1('#skF_6')))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35812,c_37312])).

tff(c_37360,plain,(
    ! [A_70241] : r1_tarski(k9_relat_1('#skF_6',A_70241),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_182,c_35812,c_35934,c_37330])).

tff(c_127,plain,(
    ! [A_60] : k2_tarski(A_60,A_60) = k1_tarski(A_60) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [D_8,B_4] : r2_hidden(D_8,k2_tarski(D_8,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_133,plain,(
    ! [A_60] : r2_hidden(A_60,k1_tarski(A_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_12])).

tff(c_35842,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35806,c_133])).

tff(c_26,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_32691,plain,(
    ! [C_58036,A_58037,B_58038] :
      ( k2_tarski(k1_funct_1(C_58036,A_58037),k1_funct_1(C_58036,B_58038)) = k9_relat_1(C_58036,k2_tarski(A_58037,B_58038))
      | ~ r2_hidden(B_58038,k1_relat_1(C_58036))
      | ~ r2_hidden(A_58037,k1_relat_1(C_58036))
      | ~ v1_funct_1(C_58036)
      | ~ v1_relat_1(C_58036) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_32722,plain,(
    ! [C_58036,B_58038] :
      ( k9_relat_1(C_58036,k2_tarski(B_58038,B_58038)) = k1_tarski(k1_funct_1(C_58036,B_58038))
      | ~ r2_hidden(B_58038,k1_relat_1(C_58036))
      | ~ r2_hidden(B_58038,k1_relat_1(C_58036))
      | ~ v1_funct_1(C_58036)
      | ~ v1_relat_1(C_58036) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32691,c_26])).

tff(c_59702,plain,(
    ! [C_99707,B_99708] :
      ( k9_relat_1(C_99707,k1_tarski(B_99708)) = k1_tarski(k1_funct_1(C_99707,B_99708))
      | ~ r2_hidden(B_99708,k1_relat_1(C_99707))
      | ~ r2_hidden(B_99708,k1_relat_1(C_99707))
      | ~ v1_funct_1(C_99707)
      | ~ v1_relat_1(C_99707) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_32722])).

tff(c_59723,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k1_tarski(k1_funct_1('#skF_6','#skF_3'))
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_35842,c_59702])).

tff(c_59784,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_92,c_35842,c_35934,c_35806,c_59723])).

tff(c_59788,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59784,c_29969])).

tff(c_59791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37360,c_59788])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.17/7.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.17/7.96  
% 17.17/7.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.29/7.96  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 17.29/7.96  
% 17.29/7.96  %Foreground sorts:
% 17.29/7.96  
% 17.29/7.96  
% 17.29/7.96  %Background operators:
% 17.29/7.96  
% 17.29/7.96  
% 17.29/7.96  %Foreground operators:
% 17.29/7.96  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 17.29/7.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 17.29/7.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.29/7.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.29/7.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.29/7.96  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 17.29/7.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.29/7.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.29/7.96  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.29/7.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 17.29/7.96  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 17.29/7.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.29/7.96  tff('#skF_5', type, '#skF_5': $i).
% 17.29/7.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 17.29/7.96  tff('#skF_6', type, '#skF_6': $i).
% 17.29/7.96  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.29/7.96  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 17.29/7.96  tff('#skF_3', type, '#skF_3': $i).
% 17.29/7.96  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 17.29/7.96  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 17.29/7.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.29/7.96  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 17.29/7.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.29/7.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.29/7.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.29/7.96  tff('#skF_4', type, '#skF_4': $i).
% 17.29/7.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.29/7.96  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 17.29/7.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 17.29/7.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.29/7.96  
% 17.34/7.98  tff(f_91, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 17.34/7.98  tff(f_147, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 17.34/7.98  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 17.34/7.98  tff(f_58, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 17.34/7.98  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 17.34/7.98  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 17.34/7.98  tff(f_52, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 17.34/7.98  tff(f_135, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 17.34/7.98  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 17.34/7.98  tff(f_60, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 17.34/7.98  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.34/7.98  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 17.34/7.98  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 17.34/7.98  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 17.34/7.98  tff(f_125, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 17.34/7.98  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 17.34/7.98  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 17.34/7.98  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 17.34/7.98  tff(f_115, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_funct_1)).
% 17.34/7.98  tff(c_62, plain, (![A_32, B_33]: (v1_relat_1(k2_zfmisc_1(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 17.34/7.98  tff(c_88, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 17.34/7.98  tff(c_170, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_77])).
% 17.34/7.98  tff(c_173, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_88, c_170])).
% 17.34/7.98  tff(c_182, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_173])).
% 17.34/7.98  tff(c_92, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 17.34/7.98  tff(c_42, plain, (![B_18]: (k2_zfmisc_1(k1_xboole_0, B_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 17.34/7.98  tff(c_445, plain, (![C_121, A_122, B_123]: (v4_relat_1(C_121, A_122) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.34/7.98  tff(c_463, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_88, c_445])).
% 17.34/7.98  tff(c_56, plain, (![B_29, A_28]: (r1_tarski(k1_relat_1(B_29), A_28) | ~v4_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_83])).
% 17.34/7.98  tff(c_271, plain, (![B_88, A_89]: (k1_tarski(B_88)=A_89 | k1_xboole_0=A_89 | ~r1_tarski(A_89, k1_tarski(B_88)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 17.34/7.98  tff(c_35008, plain, (![B_65083, B_65084]: (k1_tarski(B_65083)=k1_relat_1(B_65084) | k1_relat_1(B_65084)=k1_xboole_0 | ~v4_relat_1(B_65084, k1_tarski(B_65083)) | ~v1_relat_1(B_65084))), inference(resolution, [status(thm)], [c_56, c_271])).
% 17.34/7.98  tff(c_35068, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_463, c_35008])).
% 17.34/7.98  tff(c_35085, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_182, c_35068])).
% 17.34/7.98  tff(c_35089, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_35085])).
% 17.34/7.98  tff(c_29816, plain, (![A_47936]: (m1_subset_1(A_47936, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_47936), k2_relat_1(A_47936)))) | ~v1_funct_1(A_47936) | ~v1_relat_1(A_47936))), inference(cnfTransformation, [status(thm)], [f_135])).
% 17.34/7.98  tff(c_46, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 17.34/7.98  tff(c_29846, plain, (![A_47936]: (r1_tarski(A_47936, k2_zfmisc_1(k1_relat_1(A_47936), k2_relat_1(A_47936))) | ~v1_funct_1(A_47936) | ~v1_relat_1(A_47936))), inference(resolution, [status(thm)], [c_29816, c_46])).
% 17.34/7.98  tff(c_35123, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_6'))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_35089, c_29846])).
% 17.34/7.98  tff(c_35171, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_182, c_92, c_42, c_35123])).
% 17.34/7.98  tff(c_44, plain, (![A_19]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 17.34/7.98  tff(c_146, plain, (![A_66, B_67]: (r1_tarski(A_66, B_67) | ~m1_subset_1(A_66, k1_zfmisc_1(B_67)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 17.34/7.98  tff(c_154, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(resolution, [status(thm)], [c_44, c_146])).
% 17.34/7.98  tff(c_202, plain, (![B_75, A_76]: (B_75=A_76 | ~r1_tarski(B_75, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.34/7.98  tff(c_210, plain, (![A_19]: (k1_xboole_0=A_19 | ~r1_tarski(A_19, k1_xboole_0))), inference(resolution, [status(thm)], [c_154, c_202])).
% 17.34/7.98  tff(c_35225, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_35171, c_210])).
% 17.34/7.98  tff(c_35284, plain, (![A_19]: (r1_tarski('#skF_6', A_19))), inference(demodulation, [status(thm), theory('equality')], [c_35225, c_154])).
% 17.34/7.98  tff(c_40, plain, (![A_17]: (k2_zfmisc_1(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 17.34/7.98  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.34/7.98  tff(c_48, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 17.34/7.98  tff(c_289, plain, (![C_90, B_91, A_92]: (v5_relat_1(C_90, B_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_92, B_91))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.34/7.98  tff(c_343, plain, (![A_105, B_106, A_107]: (v5_relat_1(A_105, B_106) | ~r1_tarski(A_105, k2_zfmisc_1(A_107, B_106)))), inference(resolution, [status(thm)], [c_48, c_289])).
% 17.34/7.98  tff(c_370, plain, (![A_107, B_106]: (v5_relat_1(k2_zfmisc_1(A_107, B_106), B_106))), inference(resolution, [status(thm)], [c_6, c_343])).
% 17.34/7.98  tff(c_504, plain, (![B_125, A_126]: (r1_tarski(k2_relat_1(B_125), A_126) | ~v5_relat_1(B_125, A_126) | ~v1_relat_1(B_125))), inference(cnfTransformation, [status(thm)], [f_89])).
% 17.34/7.98  tff(c_684, plain, (![B_144]: (k2_relat_1(B_144)=k1_xboole_0 | ~v5_relat_1(B_144, k1_xboole_0) | ~v1_relat_1(B_144))), inference(resolution, [status(thm)], [c_504, c_210])).
% 17.34/7.98  tff(c_688, plain, (![A_107]: (k2_relat_1(k2_zfmisc_1(A_107, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(A_107, k1_xboole_0)))), inference(resolution, [status(thm)], [c_370, c_684])).
% 17.34/7.98  tff(c_699, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_40, c_688])).
% 17.34/7.98  tff(c_98, plain, (![B_55]: (k2_zfmisc_1(k1_xboole_0, B_55)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 17.34/7.98  tff(c_102, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_98, c_62])).
% 17.34/7.98  tff(c_466, plain, (![A_124]: (v4_relat_1(k1_xboole_0, A_124))), inference(resolution, [status(thm)], [c_44, c_445])).
% 17.34/7.98  tff(c_68, plain, (![B_39, A_38]: (k7_relat_1(B_39, A_38)=B_39 | ~v4_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_105])).
% 17.34/7.98  tff(c_469, plain, (![A_124]: (k7_relat_1(k1_xboole_0, A_124)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_466, c_68])).
% 17.34/7.98  tff(c_540, plain, (![A_127]: (k7_relat_1(k1_xboole_0, A_127)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_102, c_469])).
% 17.34/7.98  tff(c_66, plain, (![B_37, A_36]: (k2_relat_1(k7_relat_1(B_37, A_36))=k9_relat_1(B_37, A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_99])).
% 17.34/7.98  tff(c_549, plain, (![A_127]: (k9_relat_1(k1_xboole_0, A_127)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_540, c_66])).
% 17.34/7.98  tff(c_561, plain, (![A_127]: (k9_relat_1(k1_xboole_0, A_127)=k2_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_549])).
% 17.34/7.98  tff(c_704, plain, (![A_127]: (k9_relat_1(k1_xboole_0, A_127)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_699, c_561])).
% 17.34/7.98  tff(c_35268, plain, (![A_127]: (k9_relat_1('#skF_6', A_127)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_35225, c_35225, c_704])).
% 17.34/7.98  tff(c_29935, plain, (![A_47944, B_47945, C_47946, D_47947]: (k7_relset_1(A_47944, B_47945, C_47946, D_47947)=k9_relat_1(C_47946, D_47947) | ~m1_subset_1(C_47946, k1_zfmisc_1(k2_zfmisc_1(A_47944, B_47945))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 17.34/7.98  tff(c_29951, plain, (![D_47947]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_47947)=k9_relat_1('#skF_6', D_47947))), inference(resolution, [status(thm)], [c_88, c_29935])).
% 17.34/7.98  tff(c_84, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 17.34/7.98  tff(c_29969, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_29951, c_84])).
% 17.34/7.98  tff(c_35801, plain, (~r1_tarski('#skF_6', k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_35268, c_29969])).
% 17.34/7.98  tff(c_35805, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35284, c_35801])).
% 17.34/7.98  tff(c_35806, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_35085])).
% 17.34/7.98  tff(c_536, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_3'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_463, c_68])).
% 17.34/7.98  tff(c_539, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_3'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_182, c_536])).
% 17.34/7.98  tff(c_35812, plain, (k7_relat_1('#skF_6', k1_relat_1('#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_35806, c_539])).
% 17.34/7.98  tff(c_35921, plain, (k9_relat_1('#skF_6', k1_relat_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_35812, c_66])).
% 17.34/7.98  tff(c_35934, plain, (k9_relat_1('#skF_6', k1_relat_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_35921])).
% 17.34/7.98  tff(c_410, plain, (![B_117, A_118]: (k2_relat_1(k7_relat_1(B_117, A_118))=k9_relat_1(B_117, A_118) | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_99])).
% 17.34/7.98  tff(c_64, plain, (![B_35, A_34]: (r1_tarski(k9_relat_1(B_35, A_34), k2_relat_1(B_35)) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_95])).
% 17.34/7.98  tff(c_37312, plain, (![B_70239, A_70240, A_70241]: (r1_tarski(k9_relat_1(k7_relat_1(B_70239, A_70240), A_70241), k9_relat_1(B_70239, A_70240)) | ~v1_relat_1(k7_relat_1(B_70239, A_70240)) | ~v1_relat_1(B_70239))), inference(superposition, [status(thm), theory('equality')], [c_410, c_64])).
% 17.34/7.98  tff(c_37330, plain, (![A_70241]: (r1_tarski(k9_relat_1('#skF_6', A_70241), k9_relat_1('#skF_6', k1_relat_1('#skF_6'))) | ~v1_relat_1(k7_relat_1('#skF_6', k1_relat_1('#skF_6'))) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_35812, c_37312])).
% 17.34/7.98  tff(c_37360, plain, (![A_70241]: (r1_tarski(k9_relat_1('#skF_6', A_70241), k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_182, c_35812, c_35934, c_37330])).
% 17.34/7.98  tff(c_127, plain, (![A_60]: (k2_tarski(A_60, A_60)=k1_tarski(A_60))), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.34/7.98  tff(c_12, plain, (![D_8, B_4]: (r2_hidden(D_8, k2_tarski(D_8, B_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 17.34/7.98  tff(c_133, plain, (![A_60]: (r2_hidden(A_60, k1_tarski(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_12])).
% 17.34/7.98  tff(c_35842, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_35806, c_133])).
% 17.34/7.98  tff(c_26, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.34/7.98  tff(c_32691, plain, (![C_58036, A_58037, B_58038]: (k2_tarski(k1_funct_1(C_58036, A_58037), k1_funct_1(C_58036, B_58038))=k9_relat_1(C_58036, k2_tarski(A_58037, B_58038)) | ~r2_hidden(B_58038, k1_relat_1(C_58036)) | ~r2_hidden(A_58037, k1_relat_1(C_58036)) | ~v1_funct_1(C_58036) | ~v1_relat_1(C_58036))), inference(cnfTransformation, [status(thm)], [f_115])).
% 17.34/7.98  tff(c_32722, plain, (![C_58036, B_58038]: (k9_relat_1(C_58036, k2_tarski(B_58038, B_58038))=k1_tarski(k1_funct_1(C_58036, B_58038)) | ~r2_hidden(B_58038, k1_relat_1(C_58036)) | ~r2_hidden(B_58038, k1_relat_1(C_58036)) | ~v1_funct_1(C_58036) | ~v1_relat_1(C_58036))), inference(superposition, [status(thm), theory('equality')], [c_32691, c_26])).
% 17.34/7.98  tff(c_59702, plain, (![C_99707, B_99708]: (k9_relat_1(C_99707, k1_tarski(B_99708))=k1_tarski(k1_funct_1(C_99707, B_99708)) | ~r2_hidden(B_99708, k1_relat_1(C_99707)) | ~r2_hidden(B_99708, k1_relat_1(C_99707)) | ~v1_funct_1(C_99707) | ~v1_relat_1(C_99707))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_32722])).
% 17.34/7.98  tff(c_59723, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k1_tarski(k1_funct_1('#skF_6', '#skF_3')) | ~r2_hidden('#skF_3', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_35842, c_59702])).
% 17.34/7.98  tff(c_59784, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_92, c_35842, c_35934, c_35806, c_59723])).
% 17.34/7.98  tff(c_59788, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_59784, c_29969])).
% 17.34/7.98  tff(c_59791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37360, c_59788])).
% 17.34/7.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.34/7.98  
% 17.34/7.98  Inference rules
% 17.34/7.98  ----------------------
% 17.34/7.98  #Ref     : 0
% 17.34/7.98  #Sup     : 10074
% 17.34/7.98  #Fact    : 100
% 17.34/7.98  #Define  : 0
% 17.34/7.98  #Split   : 60
% 17.34/7.98  #Chain   : 0
% 17.34/7.98  #Close   : 0
% 17.34/7.98  
% 17.34/7.98  Ordering : KBO
% 17.34/7.98  
% 17.34/7.98  Simplification rules
% 17.34/7.98  ----------------------
% 17.34/7.98  #Subsume      : 4836
% 17.34/7.98  #Demod        : 7600
% 17.34/7.98  #Tautology    : 3381
% 17.34/7.98  #SimpNegUnit  : 512
% 17.34/7.98  #BackRed      : 296
% 17.34/7.98  
% 17.34/7.98  #Partial instantiations: 52352
% 17.34/7.98  #Strategies tried      : 1
% 17.34/7.98  
% 17.34/7.98  Timing (in seconds)
% 17.34/7.98  ----------------------
% 17.34/7.98  Preprocessing        : 0.35
% 17.34/7.98  Parsing              : 0.18
% 17.34/7.98  CNF conversion       : 0.03
% 17.34/7.98  Main loop            : 6.79
% 17.34/7.98  Inferencing          : 2.32
% 17.34/7.98  Reduction            : 2.23
% 17.34/7.98  Demodulation         : 1.67
% 17.34/7.98  BG Simplification    : 0.17
% 17.34/7.98  Subsumption          : 1.69
% 17.34/7.98  Abstraction          : 0.24
% 17.34/7.98  MUC search           : 0.00
% 17.34/7.98  Cooper               : 0.00
% 17.34/7.98  Total                : 7.19
% 17.34/7.98  Index Insertion      : 0.00
% 17.34/7.98  Index Deletion       : 0.00
% 17.34/7.98  Index Matching       : 0.00
% 17.34/7.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
