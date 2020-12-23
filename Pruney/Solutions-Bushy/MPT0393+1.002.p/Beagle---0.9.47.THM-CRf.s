%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0393+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:14 EST 2020

% Result     : Theorem 12.26s
% Output     : CNFRefutation 12.26s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 612 expanded)
%              Number of leaves         :   32 ( 215 expanded)
%              Depth                    :   17
%              Number of atoms          :  238 (1532 expanded)
%              Number of equality atoms :   64 ( 575 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_8 > #skF_3 > #skF_9 > #skF_2 > #skF_7 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_64,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(c_32,plain,(
    ! [C_26] : r2_hidden(C_26,k1_tarski(C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_48,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_71,plain,(
    ! [A_44] :
      ( k1_xboole_0 = A_44
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_75,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_71])).

tff(c_76,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_48])).

tff(c_46,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_7'(A_27,B_28),A_27)
      | r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_50,plain,(
    ! [A_32] : m1_subset_1('#skF_8'(A_32),A_32) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_199,plain,(
    ! [C_75,B_76,A_77] :
      ( ~ v1_xboole_0(C_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(C_75))
      | ~ r2_hidden(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_210,plain,(
    ! [C_78,A_79] :
      ( ~ v1_xboole_0(C_78)
      | ~ r2_hidden(A_79,'#skF_8'(k1_zfmisc_1(C_78))) ) ),
    inference(resolution,[status(thm)],[c_50,c_199])).

tff(c_219,plain,(
    ! [C_80,B_81] :
      ( ~ v1_xboole_0(C_80)
      | r1_tarski('#skF_8'(k1_zfmisc_1(C_80)),B_81) ) ),
    inference(resolution,[status(thm)],[c_46,c_210])).

tff(c_111,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_7'(A_56,B_57),A_56)
      | r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_60,plain,(
    ! [B_41,A_40] :
      ( ~ v1_xboole_0(B_41)
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_120,plain,(
    ! [A_56,B_57] :
      ( ~ v1_xboole_0(A_56)
      | r1_tarski(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_111,c_60])).

tff(c_129,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_136,plain,(
    ! [B_57,A_56] :
      ( B_57 = A_56
      | ~ r1_tarski(B_57,A_56)
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_120,c_129])).

tff(c_262,plain,(
    ! [B_92,C_93] :
      ( B_92 = '#skF_8'(k1_zfmisc_1(C_93))
      | ~ v1_xboole_0(B_92)
      | ~ v1_xboole_0(C_93) ) ),
    inference(resolution,[status(thm)],[c_219,c_136])).

tff(c_266,plain,(
    ! [C_94] :
      ( '#skF_8'(k1_zfmisc_1(C_94)) = k1_xboole_0
      | ~ v1_xboole_0(C_94) ) ),
    inference(resolution,[status(thm)],[c_76,c_262])).

tff(c_99,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_104,plain,(
    ! [B_52] : r1_tarski('#skF_8'(k1_zfmisc_1(B_52)),B_52) ),
    inference(resolution,[status(thm)],[c_50,c_99])).

tff(c_293,plain,(
    ! [C_95] :
      ( r1_tarski(k1_xboole_0,C_95)
      | ~ v1_xboole_0(C_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_104])).

tff(c_54,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(A_34,k1_zfmisc_1(B_35))
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_230,plain,(
    ! [B_82,A_83,A_84] :
      ( ~ v1_xboole_0(B_82)
      | ~ r2_hidden(A_83,A_84)
      | ~ r1_tarski(A_84,B_82) ) ),
    inference(resolution,[status(thm)],[c_54,c_199])).

tff(c_235,plain,(
    ! [B_82,A_27,B_28] :
      ( ~ v1_xboole_0(B_82)
      | ~ r1_tarski(A_27,B_82)
      | r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_46,c_230])).

tff(c_301,plain,(
    ! [B_28,C_95] :
      ( r1_tarski(k1_xboole_0,B_28)
      | ~ v1_xboole_0(C_95) ) ),
    inference(resolution,[status(thm)],[c_293,c_235])).

tff(c_311,plain,(
    ! [C_95] : ~ v1_xboole_0(C_95) ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_76])).

tff(c_314,plain,(
    ! [B_28] : r1_tarski(k1_xboole_0,B_28) ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_1353,plain,(
    ! [A_158,B_159,D_160] :
      ( r2_hidden('#skF_2'(A_158,B_159),D_160)
      | ~ r2_hidden(D_160,A_158)
      | r2_hidden('#skF_4'(A_158,B_159),A_158)
      | k1_setfam_1(A_158) = B_159
      | k1_xboole_0 = A_158 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_2'(A_3,B_4),B_4)
      | r2_hidden('#skF_4'(A_3,B_4),A_3)
      | k1_setfam_1(A_3) = B_4
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1909,plain,(
    ! [D_189,A_190] :
      ( ~ r2_hidden(D_189,A_190)
      | r2_hidden('#skF_4'(A_190,D_189),A_190)
      | k1_setfam_1(A_190) = D_189
      | k1_xboole_0 = A_190 ) ),
    inference(resolution,[status(thm)],[c_1353,c_12])).

tff(c_30,plain,(
    ! [C_26,A_22] :
      ( C_26 = A_22
      | ~ r2_hidden(C_26,k1_tarski(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_35463,plain,(
    ! [A_691,D_692] :
      ( '#skF_4'(k1_tarski(A_691),D_692) = A_691
      | ~ r2_hidden(D_692,k1_tarski(A_691))
      | k1_setfam_1(k1_tarski(A_691)) = D_692
      | k1_tarski(A_691) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1909,c_30])).

tff(c_36025,plain,(
    ! [C_698] :
      ( '#skF_4'(k1_tarski(C_698),C_698) = C_698
      | k1_setfam_1(k1_tarski(C_698)) = C_698
      | k1_tarski(C_698) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_35463])).

tff(c_62,plain,(
    k1_setfam_1(k1_tarski('#skF_9')) != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36234,plain,
    ( '#skF_4'(k1_tarski('#skF_9'),'#skF_9') = '#skF_9'
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36025,c_62])).

tff(c_36240,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36234])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_142,plain,(
    ! [C_64,B_65,A_66] :
      ( r2_hidden(C_64,B_65)
      | ~ r2_hidden(C_64,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_931,plain,(
    ! [A_135,B_136,B_137] :
      ( r2_hidden('#skF_7'(A_135,B_136),B_137)
      | ~ r1_tarski(A_135,B_137)
      | r1_tarski(A_135,B_136) ) ),
    inference(resolution,[status(thm)],[c_46,c_142])).

tff(c_42,plain,(
    ! [C_31,B_28,A_27] :
      ( r2_hidden(C_31,B_28)
      | ~ r2_hidden(C_31,A_27)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5061,plain,(
    ! [A_292,B_293,B_294,B_295] :
      ( r2_hidden('#skF_7'(A_292,B_293),B_294)
      | ~ r1_tarski(B_295,B_294)
      | ~ r1_tarski(A_292,B_295)
      | r1_tarski(A_292,B_293) ) ),
    inference(resolution,[status(thm)],[c_931,c_42])).

tff(c_5092,plain,(
    ! [A_296,B_297,B_298] :
      ( r2_hidden('#skF_7'(A_296,B_297),B_298)
      | ~ r1_tarski(A_296,'#skF_8'(k1_zfmisc_1(B_298)))
      | r1_tarski(A_296,B_297) ) ),
    inference(resolution,[status(thm)],[c_104,c_5061])).

tff(c_5155,plain,(
    ! [B_299,B_300] :
      ( r2_hidden('#skF_7'('#skF_8'(k1_zfmisc_1(B_299)),B_300),B_299)
      | r1_tarski('#skF_8'(k1_zfmisc_1(B_299)),B_300) ) ),
    inference(resolution,[status(thm)],[c_6,c_5092])).

tff(c_13298,plain,(
    ! [B_446,B_447,B_448] :
      ( r2_hidden('#skF_7'('#skF_8'(k1_zfmisc_1(B_446)),B_447),B_448)
      | ~ r1_tarski(B_446,B_448)
      | r1_tarski('#skF_8'(k1_zfmisc_1(B_446)),B_447) ) ),
    inference(resolution,[status(thm)],[c_5155,c_42])).

tff(c_44,plain,(
    ! [A_27,B_28] :
      ( ~ r2_hidden('#skF_7'(A_27,B_28),B_28)
      | r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_13444,plain,(
    ! [B_449,B_450] :
      ( ~ r1_tarski(B_449,B_450)
      | r1_tarski('#skF_8'(k1_zfmisc_1(B_449)),B_450) ) ),
    inference(resolution,[status(thm)],[c_13298,c_44])).

tff(c_316,plain,(
    ! [B_99] : r1_tarski(k1_xboole_0,B_99) ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_327,plain,(
    ! [B_99] :
      ( k1_xboole_0 = B_99
      | ~ r1_tarski(B_99,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_316,c_2])).

tff(c_13636,plain,(
    ! [B_451] :
      ( '#skF_8'(k1_zfmisc_1(B_451)) = k1_xboole_0
      | ~ r1_tarski(B_451,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_13444,c_327])).

tff(c_137,plain,(
    ! [B_52] :
      ( '#skF_8'(k1_zfmisc_1(B_52)) = B_52
      | ~ r1_tarski(B_52,'#skF_8'(k1_zfmisc_1(B_52))) ) ),
    inference(resolution,[status(thm)],[c_104,c_129])).

tff(c_15106,plain,(
    ! [B_467] :
      ( '#skF_8'(k1_zfmisc_1(B_467)) = B_467
      | ~ r1_tarski(B_467,k1_xboole_0)
      | ~ r1_tarski(B_467,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13636,c_137])).

tff(c_15436,plain,(
    ! [B_467] :
      ( '#skF_8'(k1_zfmisc_1(B_467)) = B_467
      | ~ r1_tarski(B_467,B_467)
      | ~ r1_tarski(B_467,k1_xboole_0)
      | ~ r1_tarski(B_467,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15106,c_137])).

tff(c_15536,plain,(
    ! [B_467] :
      ( '#skF_8'(k1_zfmisc_1(B_467)) = B_467
      | ~ r1_tarski(B_467,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_15436])).

tff(c_265,plain,(
    ! [C_93] :
      ( '#skF_8'(k1_zfmisc_1(C_93)) = k1_xboole_0
      | ~ v1_xboole_0(C_93) ) ),
    inference(resolution,[status(thm)],[c_76,c_262])).

tff(c_1504,plain,(
    ! [B_171,C_172] :
      ( B_171 = '#skF_8'(k1_zfmisc_1(C_172))
      | ~ r1_tarski(B_171,'#skF_8'(k1_zfmisc_1(C_172)))
      | ~ v1_xboole_0(C_172) ) ),
    inference(resolution,[status(thm)],[c_219,c_2])).

tff(c_1528,plain,(
    ! [B_171,C_93] :
      ( B_171 = '#skF_8'(k1_zfmisc_1(C_93))
      | ~ r1_tarski(B_171,k1_xboole_0)
      | ~ v1_xboole_0(C_93)
      | ~ v1_xboole_0(C_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_1504])).

tff(c_16115,plain,(
    ! [C_476,B_477] :
      ( '#skF_8'(k1_zfmisc_1(C_476)) = '#skF_8'(k1_zfmisc_1(B_477))
      | ~ v1_xboole_0(C_476)
      | ~ r1_tarski(B_477,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_13444,c_1528])).

tff(c_17839,plain,(
    ! [B_484,C_485] :
      ( m1_subset_1('#skF_8'(k1_zfmisc_1(B_484)),k1_zfmisc_1(C_485))
      | ~ v1_xboole_0(C_485)
      | ~ r1_tarski(B_484,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16115,c_50])).

tff(c_56,plain,(
    ! [C_38,B_37,A_36] :
      ( ~ v1_xboole_0(C_38)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(C_38))
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_17920,plain,(
    ! [A_36,B_484,C_485] :
      ( ~ r2_hidden(A_36,'#skF_8'(k1_zfmisc_1(B_484)))
      | ~ v1_xboole_0(C_485)
      | ~ r1_tarski(B_484,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_17839,c_56])).

tff(c_17925,plain,(
    ! [A_486,B_487] :
      ( ~ r2_hidden(A_486,'#skF_8'(k1_zfmisc_1(B_487)))
      | ~ r1_tarski(B_487,k1_xboole_0) ) ),
    inference(splitLeft,[status(thm)],[c_17920])).

tff(c_18244,plain,(
    ! [A_491,B_492] :
      ( ~ r2_hidden(A_491,B_492)
      | ~ r1_tarski(B_492,k1_xboole_0)
      | ~ r1_tarski(B_492,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15536,c_17925])).

tff(c_18352,plain,(
    ! [C_26] : ~ r1_tarski(k1_tarski(C_26),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_18244])).

tff(c_36303,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36240,c_18352])).

tff(c_36481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_36303])).

tff(c_36483,plain,(
    k1_tarski('#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36234])).

tff(c_36482,plain,(
    '#skF_4'(k1_tarski('#skF_9'),'#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_36234])).

tff(c_18,plain,(
    ! [A_3,B_4,D_20] :
      ( r2_hidden('#skF_2'(A_3,B_4),D_20)
      | ~ r2_hidden(D_20,A_3)
      | r2_hidden('#skF_3'(A_3,B_4),B_4)
      | k1_setfam_1(A_3) = B_4
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_2'(A_3,B_4),B_4)
      | ~ r2_hidden('#skF_3'(A_3,B_4),'#skF_4'(A_3,B_4))
      | k1_setfam_1(A_3) = B_4
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36502,plain,
    ( ~ r2_hidden('#skF_2'(k1_tarski('#skF_9'),'#skF_9'),'#skF_9')
    | ~ r2_hidden('#skF_3'(k1_tarski('#skF_9'),'#skF_9'),'#skF_9')
    | k1_setfam_1(k1_tarski('#skF_9')) = '#skF_9'
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36482,c_8])).

tff(c_36515,plain,
    ( ~ r2_hidden('#skF_2'(k1_tarski('#skF_9'),'#skF_9'),'#skF_9')
    | ~ r2_hidden('#skF_3'(k1_tarski('#skF_9'),'#skF_9'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_36483,c_62,c_36502])).

tff(c_36768,plain,(
    ~ r2_hidden('#skF_3'(k1_tarski('#skF_9'),'#skF_9'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_36515])).

tff(c_36778,plain,(
    ! [D_20] :
      ( r2_hidden('#skF_2'(k1_tarski('#skF_9'),'#skF_9'),D_20)
      | ~ r2_hidden(D_20,k1_tarski('#skF_9'))
      | k1_setfam_1(k1_tarski('#skF_9')) = '#skF_9'
      | k1_tarski('#skF_9') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_36768])).

tff(c_36818,plain,(
    ! [D_704] :
      ( r2_hidden('#skF_2'(k1_tarski('#skF_9'),'#skF_9'),D_704)
      | ~ r2_hidden(D_704,k1_tarski('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36483,c_62,c_36778])).

tff(c_16,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_2'(A_3,B_4),B_4)
      | r2_hidden('#skF_3'(A_3,B_4),B_4)
      | k1_setfam_1(A_3) = B_4
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36781,plain,
    ( ~ r2_hidden('#skF_2'(k1_tarski('#skF_9'),'#skF_9'),'#skF_9')
    | k1_setfam_1(k1_tarski('#skF_9')) = '#skF_9'
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_36768])).

tff(c_36793,plain,(
    ~ r2_hidden('#skF_2'(k1_tarski('#skF_9'),'#skF_9'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_36483,c_62,c_36781])).

tff(c_36821,plain,(
    ~ r2_hidden('#skF_9',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_36818,c_36793])).

tff(c_36917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36821])).

tff(c_36919,plain,(
    r2_hidden('#skF_3'(k1_tarski('#skF_9'),'#skF_9'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_36515])).

tff(c_37103,plain,(
    ! [B_709] :
      ( r2_hidden('#skF_3'(k1_tarski('#skF_9'),'#skF_9'),B_709)
      | ~ r1_tarski('#skF_9',B_709) ) ),
    inference(resolution,[status(thm)],[c_36919,c_42])).

tff(c_10,plain,(
    ! [A_3,B_4,D_20] :
      ( r2_hidden('#skF_2'(A_3,B_4),D_20)
      | ~ r2_hidden(D_20,A_3)
      | ~ r2_hidden('#skF_3'(A_3,B_4),'#skF_4'(A_3,B_4))
      | k1_setfam_1(A_3) = B_4
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_37165,plain,(
    ! [D_20] :
      ( r2_hidden('#skF_2'(k1_tarski('#skF_9'),'#skF_9'),D_20)
      | ~ r2_hidden(D_20,k1_tarski('#skF_9'))
      | k1_setfam_1(k1_tarski('#skF_9')) = '#skF_9'
      | k1_tarski('#skF_9') = k1_xboole_0
      | ~ r1_tarski('#skF_9','#skF_4'(k1_tarski('#skF_9'),'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_37103,c_10])).

tff(c_37220,plain,(
    ! [D_20] :
      ( r2_hidden('#skF_2'(k1_tarski('#skF_9'),'#skF_9'),D_20)
      | ~ r2_hidden(D_20,k1_tarski('#skF_9'))
      | k1_setfam_1(k1_tarski('#skF_9')) = '#skF_9'
      | k1_tarski('#skF_9') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_36482,c_37165])).

tff(c_37235,plain,(
    ! [D_710] :
      ( r2_hidden('#skF_2'(k1_tarski('#skF_9'),'#skF_9'),D_710)
      | ~ r2_hidden(D_710,k1_tarski('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36483,c_62,c_37220])).

tff(c_36918,plain,(
    ~ r2_hidden('#skF_2'(k1_tarski('#skF_9'),'#skF_9'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_36515])).

tff(c_37240,plain,(
    ~ r2_hidden('#skF_9',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_37235,c_36918])).

tff(c_37337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_37240])).

tff(c_37338,plain,(
    ! [C_485] : ~ v1_xboole_0(C_485) ),
    inference(splitRight,[status(thm)],[c_17920])).

tff(c_37340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37338,c_76])).

%------------------------------------------------------------------------------
