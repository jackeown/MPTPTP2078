%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0389+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:13 EST 2020

% Result     : Theorem 17.91s
% Output     : CNFRefutation 17.91s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 226 expanded)
%              Number of leaves         :   28 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          :  153 ( 520 expanded)
%              Number of equality atoms :   28 (  78 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ( A = k1_xboole_0
          | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_48,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_56,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(c_50,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_8'),k1_setfam_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_108,plain,(
    ! [A_58,B_59] :
      ( r2_hidden('#skF_5'(A_58,B_59),A_58)
      | r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_36,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(A_29,B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_120,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1('#skF_5'(A_58,B_59),A_58)
      | r1_tarski(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_108,c_36])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden('#skF_5'(A_22,B_23),B_23)
      | r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_118,plain,(
    ! [A_58] : r1_tarski(A_58,A_58) ),
    inference(resolution,[status(thm)],[c_108,c_28])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( r2_hidden('#skF_5'(A_22,B_23),A_22)
      | r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(A_33,k1_zfmisc_1(B_34))
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_150,plain,(
    ! [C_70,B_71,A_72] :
      ( ~ v1_xboole_0(C_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(C_70))
      | ~ r2_hidden(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_181,plain,(
    ! [B_80,A_81,A_82] :
      ( ~ v1_xboole_0(B_80)
      | ~ r2_hidden(A_81,A_82)
      | ~ r1_tarski(A_82,B_80) ) ),
    inference(resolution,[status(thm)],[c_42,c_150])).

tff(c_188,plain,(
    ! [B_83,A_84,B_85] :
      ( ~ v1_xboole_0(B_83)
      | ~ r1_tarski(A_84,B_83)
      | r1_tarski(A_84,B_85) ) ),
    inference(resolution,[status(thm)],[c_30,c_181])).

tff(c_202,plain,(
    ! [A_86,B_87] :
      ( ~ v1_xboole_0(A_86)
      | r1_tarski(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_118,c_188])).

tff(c_209,plain,(
    ~ v1_xboole_0(k1_setfam_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_202,c_50])).

tff(c_54,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_200,plain,(
    ! [B_85] :
      ( ~ v1_xboole_0('#skF_8')
      | r1_tarski('#skF_7',B_85) ) ),
    inference(resolution,[status(thm)],[c_54,c_188])).

tff(c_201,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_38,plain,(
    ! [A_31,B_32] :
      ( r2_hidden(A_31,B_32)
      | v1_xboole_0(B_32)
      | ~ m1_subset_1(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_122,plain,(
    ! [C_61,B_62,A_63] :
      ( r2_hidden(C_61,B_62)
      | ~ r2_hidden(C_61,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_371,plain,(
    ! [A_110,B_111,B_112] :
      ( r2_hidden(A_110,B_111)
      | ~ r1_tarski(B_112,B_111)
      | v1_xboole_0(B_112)
      | ~ m1_subset_1(A_110,B_112) ) ),
    inference(resolution,[status(thm)],[c_38,c_122])).

tff(c_392,plain,(
    ! [A_110] :
      ( r2_hidden(A_110,'#skF_8')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_110,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_54,c_371])).

tff(c_393,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_392])).

tff(c_46,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_403,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_393,c_46])).

tff(c_408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_403])).

tff(c_411,plain,(
    ! [A_115] :
      ( r2_hidden(A_115,'#skF_8')
      | ~ m1_subset_1(A_115,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_392])).

tff(c_16,plain,(
    ! [C_15,D_18,A_3] :
      ( r2_hidden(C_15,D_18)
      | ~ r2_hidden(D_18,A_3)
      | ~ r2_hidden(C_15,k1_setfam_1(A_3))
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_431,plain,(
    ! [C_15,A_115] :
      ( r2_hidden(C_15,A_115)
      | ~ r2_hidden(C_15,k1_setfam_1('#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | ~ m1_subset_1(A_115,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_411,c_16])).

tff(c_764,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_431])).

tff(c_32,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_60,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_64,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_60])).

tff(c_66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_32])).

tff(c_771,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_66])).

tff(c_777,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_771])).

tff(c_779,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_431])).

tff(c_226,plain,(
    ! [A_92,C_93] :
      ( r2_hidden('#skF_1'(A_92,k1_setfam_1(A_92),C_93),A_92)
      | r2_hidden(C_93,k1_setfam_1(A_92))
      | k1_xboole_0 = A_92 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1440,plain,(
    ! [A_179,C_180] :
      ( m1_subset_1('#skF_1'(A_179,k1_setfam_1(A_179),C_180),A_179)
      | r2_hidden(C_180,k1_setfam_1(A_179))
      | k1_xboole_0 = A_179 ) ),
    inference(resolution,[status(thm)],[c_226,c_36])).

tff(c_436,plain,(
    ! [A_115] :
      ( m1_subset_1(A_115,'#skF_8')
      | ~ m1_subset_1(A_115,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_411,c_36])).

tff(c_1451,plain,(
    ! [C_180] :
      ( m1_subset_1('#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_180),'#skF_8')
      | r2_hidden(C_180,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_1440,c_436])).

tff(c_1470,plain,(
    ! [C_180] :
      ( m1_subset_1('#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_180),'#skF_8')
      | r2_hidden(C_180,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1451])).

tff(c_173,plain,(
    ! [C_75,D_76,A_77] :
      ( r2_hidden(C_75,D_76)
      | ~ r2_hidden(D_76,A_77)
      | ~ r2_hidden(C_75,k1_setfam_1(A_77))
      | k1_xboole_0 = A_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2165,plain,(
    ! [C_209,A_210,B_211] :
      ( r2_hidden(C_209,A_210)
      | ~ r2_hidden(C_209,k1_setfam_1(B_211))
      | k1_xboole_0 = B_211
      | v1_xboole_0(B_211)
      | ~ m1_subset_1(A_210,B_211) ) ),
    inference(resolution,[status(thm)],[c_38,c_173])).

tff(c_28679,plain,(
    ! [A_749,A_750,B_751] :
      ( r2_hidden(A_749,A_750)
      | k1_xboole_0 = B_751
      | v1_xboole_0(B_751)
      | ~ m1_subset_1(A_750,B_751)
      | v1_xboole_0(k1_setfam_1(B_751))
      | ~ m1_subset_1(A_749,k1_setfam_1(B_751)) ) ),
    inference(resolution,[status(thm)],[c_38,c_2165])).

tff(c_28777,plain,(
    ! [A_749,C_180] :
      ( r2_hidden(A_749,'#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_180))
      | k1_xboole_0 = '#skF_8'
      | v1_xboole_0('#skF_8')
      | v1_xboole_0(k1_setfam_1('#skF_8'))
      | ~ m1_subset_1(A_749,k1_setfam_1('#skF_8'))
      | r2_hidden(C_180,k1_setfam_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_1470,c_28679])).

tff(c_45447,plain,(
    ! [A_985,C_986] :
      ( r2_hidden(A_985,'#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_986))
      | ~ m1_subset_1(A_985,k1_setfam_1('#skF_8'))
      | r2_hidden(C_986,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_201,c_779,c_28777])).

tff(c_18,plain,(
    ! [C_15,A_3] :
      ( ~ r2_hidden(C_15,'#skF_1'(A_3,k1_setfam_1(A_3),C_15))
      | r2_hidden(C_15,k1_setfam_1(A_3))
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_45549,plain,(
    ! [C_986] :
      ( k1_xboole_0 = '#skF_7'
      | ~ m1_subset_1(C_986,k1_setfam_1('#skF_8'))
      | r2_hidden(C_986,k1_setfam_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_45447,c_18])).

tff(c_45608,plain,(
    ! [C_987] :
      ( ~ m1_subset_1(C_987,k1_setfam_1('#skF_8'))
      | r2_hidden(C_987,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_45549])).

tff(c_46550,plain,(
    ! [A_998] :
      ( r1_tarski(A_998,k1_setfam_1('#skF_7'))
      | ~ m1_subset_1('#skF_5'(A_998,k1_setfam_1('#skF_7')),k1_setfam_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_45608,c_28])).

tff(c_46562,plain,(
    r1_tarski(k1_setfam_1('#skF_8'),k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_120,c_46550])).

tff(c_46567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_46562])).

tff(c_46569,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_46653,plain,(
    ! [A_1005,B_1006] :
      ( ~ v1_xboole_0(A_1005)
      | r1_tarski(A_1005,B_1006) ) ),
    inference(resolution,[status(thm)],[c_118,c_188])).

tff(c_46607,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_46569,c_46])).

tff(c_24,plain,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_46613,plain,(
    k1_setfam_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46607,c_46607,c_24])).

tff(c_46630,plain,(
    ~ r1_tarski('#skF_8',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46613,c_50])).

tff(c_46656,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_46653,c_46630])).

tff(c_46662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46569,c_46656])).

%------------------------------------------------------------------------------
