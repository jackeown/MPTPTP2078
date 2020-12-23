%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:13 EST 2020

% Result     : Theorem 11.21s
% Output     : CNFRefutation 11.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 188 expanded)
%              Number of leaves         :   37 (  77 expanded)
%              Depth                    :   21
%              Number of atoms          :   91 ( 190 expanded)
%              Number of equality atoms :   56 ( 153 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_82,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_84,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_72,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k2_tarski(H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E,F,G,H,I,J] :
      ( J = k7_enumset1(A,B,C,D,E,F,G,H,I)
    <=> ! [K] :
          ( r2_hidden(K,J)
        <=> ~ ( K != A
              & K != B
              & K != C
              & K != D
              & K != E
              & K != F
              & K != G
              & K != H
              & K != I ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_enumset1)).

tff(f_90,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_94,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_72,plain,(
    ! [A_39,B_40] : k1_enumset1(A_39,A_39,B_40) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_74,plain,(
    ! [A_41,B_42,C_43] : k2_enumset1(A_41,A_41,B_42,C_43) = k1_enumset1(A_41,B_42,C_43) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_76,plain,(
    ! [A_44,B_45,C_46,D_47] : k3_enumset1(A_44,A_44,B_45,C_46,D_47) = k2_enumset1(A_44,B_45,C_46,D_47) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_78,plain,(
    ! [B_49,A_48,D_51,E_52,C_50] : k4_enumset1(A_48,A_48,B_49,C_50,D_51,E_52) = k3_enumset1(A_48,B_49,C_50,D_51,E_52) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_80,plain,(
    ! [A_53,D_56,E_57,C_55,F_58,B_54] : k5_enumset1(A_53,A_53,B_54,C_55,D_56,E_57,F_58) = k4_enumset1(A_53,B_54,C_55,D_56,E_57,F_58) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_82,plain,(
    ! [F_64,D_62,A_59,G_65,C_61,E_63,B_60] : k6_enumset1(A_59,A_59,B_60,C_61,D_62,E_63,F_64,G_65) = k5_enumset1(A_59,B_60,C_61,D_62,E_63,F_64,G_65) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1689,plain,(
    ! [G_455,B_450,E_453,D_454,A_452,F_451,H_448,C_449] : k2_xboole_0(k5_enumset1(A_452,B_450,C_449,D_454,E_453,F_451,G_455),k1_tarski(H_448)) = k6_enumset1(A_452,B_450,C_449,D_454,E_453,F_451,G_455,H_448) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1703,plain,(
    ! [A_53,D_56,E_57,C_55,F_58,H_448,B_54] : k6_enumset1(A_53,A_53,B_54,C_55,D_56,E_57,F_58,H_448) = k2_xboole_0(k4_enumset1(A_53,B_54,C_55,D_56,E_57,F_58),k1_tarski(H_448)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_1689])).

tff(c_7736,plain,(
    ! [D_1626,B_1627,A_1623,H_1624,C_1622,E_1625,F_1628] : k2_xboole_0(k4_enumset1(A_1623,B_1627,C_1622,D_1626,E_1625,F_1628),k1_tarski(H_1624)) = k5_enumset1(A_1623,B_1627,C_1622,D_1626,E_1625,F_1628,H_1624) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1703])).

tff(c_7752,plain,(
    ! [B_49,A_48,D_51,E_52,C_50,H_1624] : k5_enumset1(A_48,A_48,B_49,C_50,D_51,E_52,H_1624) = k2_xboole_0(k3_enumset1(A_48,B_49,C_50,D_51,E_52),k1_tarski(H_1624)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_7736])).

tff(c_7756,plain,(
    ! [D_1629,A_1631,E_1633,H_1634,C_1632,B_1630] : k2_xboole_0(k3_enumset1(A_1631,B_1630,C_1632,D_1629,E_1633),k1_tarski(H_1634)) = k4_enumset1(A_1631,B_1630,C_1632,D_1629,E_1633,H_1634) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_7752])).

tff(c_7772,plain,(
    ! [C_46,H_1634,A_44,B_45,D_47] : k4_enumset1(A_44,A_44,B_45,C_46,D_47,H_1634) = k2_xboole_0(k2_enumset1(A_44,B_45,C_46,D_47),k1_tarski(H_1634)) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_7756])).

tff(c_7776,plain,(
    ! [B_1638,A_1639,C_1637,H_1635,D_1636] : k2_xboole_0(k2_enumset1(A_1639,B_1638,C_1637,D_1636),k1_tarski(H_1635)) = k3_enumset1(A_1639,B_1638,C_1637,D_1636,H_1635) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_7772])).

tff(c_7801,plain,(
    ! [A_41,B_42,C_43,H_1635] : k3_enumset1(A_41,A_41,B_42,C_43,H_1635) = k2_xboole_0(k1_enumset1(A_41,B_42,C_43),k1_tarski(H_1635)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_7776])).

tff(c_7806,plain,(
    ! [A_1650,B_1651,C_1652,H_1653] : k2_xboole_0(k1_enumset1(A_1650,B_1651,C_1652),k1_tarski(H_1653)) = k2_enumset1(A_1650,B_1651,C_1652,H_1653) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7801])).

tff(c_7828,plain,(
    ! [A_39,B_40,H_1653] : k2_xboole_0(k2_tarski(A_39,B_40),k1_tarski(H_1653)) = k2_enumset1(A_39,A_39,B_40,H_1653) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_7806])).

tff(c_7831,plain,(
    ! [A_39,B_40,H_1653] : k2_xboole_0(k2_tarski(A_39,B_40),k1_tarski(H_1653)) = k1_enumset1(A_39,B_40,H_1653) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_7828])).

tff(c_200,plain,(
    ! [D_103,C_104,B_105,A_106] : k2_enumset1(D_103,C_104,B_105,A_106) = k2_enumset1(A_106,B_105,C_104,D_103) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_247,plain,(
    ! [D_107,C_108,B_109] : k2_enumset1(D_107,C_108,B_109,B_109) = k1_enumset1(B_109,C_108,D_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_74])).

tff(c_260,plain,(
    ! [C_108,B_109] : k1_enumset1(C_108,B_109,B_109) = k1_enumset1(B_109,C_108,C_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_74])).

tff(c_7968,plain,(
    ! [C_1664,B_1665,H_1666] : k2_xboole_0(k1_enumset1(C_1664,B_1665,B_1665),k1_tarski(H_1666)) = k2_enumset1(B_1665,C_1664,C_1664,H_1666) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_7806])).

tff(c_7804,plain,(
    ! [A_41,B_42,C_43,H_1635] : k2_xboole_0(k1_enumset1(A_41,B_42,C_43),k1_tarski(H_1635)) = k2_enumset1(A_41,B_42,C_43,H_1635) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7801])).

tff(c_8040,plain,(
    ! [C_1667,B_1668,H_1669] : k2_enumset1(C_1667,B_1668,B_1668,H_1669) = k2_enumset1(B_1668,C_1667,C_1667,H_1669) ),
    inference(superposition,[status(thm),theory(equality)],[c_7968,c_7804])).

tff(c_216,plain,(
    ! [D_103,C_104,B_105] : k2_enumset1(D_103,C_104,B_105,B_105) = k1_enumset1(B_105,C_104,D_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_74])).

tff(c_8068,plain,(
    ! [H_1669,B_1668] : k2_enumset1(H_1669,B_1668,B_1668,H_1669) = k1_enumset1(H_1669,H_1669,B_1668) ),
    inference(superposition,[status(thm),theory(equality)],[c_8040,c_216])).

tff(c_8144,plain,(
    ! [H_1680,B_1681] : k2_enumset1(H_1680,B_1681,B_1681,H_1680) = k2_tarski(H_1680,B_1681) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_8068])).

tff(c_7775,plain,(
    ! [C_46,H_1634,A_44,B_45,D_47] : k2_xboole_0(k2_enumset1(A_44,B_45,C_46,D_47),k1_tarski(H_1634)) = k3_enumset1(A_44,B_45,C_46,D_47,H_1634) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_7772])).

tff(c_8159,plain,(
    ! [H_1680,B_1681,H_1634] : k3_enumset1(H_1680,B_1681,B_1681,H_1680,H_1634) = k2_xboole_0(k2_tarski(H_1680,B_1681),k1_tarski(H_1634)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8144,c_7775])).

tff(c_8192,plain,(
    ! [H_1680,B_1681,H_1634] : k3_enumset1(H_1680,B_1681,B_1681,H_1680,H_1634) = k1_enumset1(H_1680,B_1681,H_1634) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7831,c_8159])).

tff(c_68,plain,(
    ! [D_33,A_30,C_32,H_37,B_31,E_34,G_36,F_35] : k2_xboole_0(k5_enumset1(A_30,B_31,C_32,D_33,E_34,F_35,G_36),k1_tarski(H_37)) = k6_enumset1(A_30,B_31,C_32,D_33,E_34,F_35,G_36,H_37) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_70,plain,(
    ! [A_38] : k2_tarski(A_38,A_38) = k1_tarski(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2129,plain,(
    ! [G_532,F_538,E_540,H_536,D_535,I_533,C_537,A_534,B_539] : k2_xboole_0(k5_enumset1(A_534,B_539,C_537,D_535,E_540,F_538,G_532),k2_tarski(H_536,I_533)) = k7_enumset1(A_534,B_539,C_537,D_535,E_540,F_538,G_532,H_536,I_533) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2146,plain,(
    ! [G_532,F_538,E_540,D_535,C_537,A_534,A_38,B_539] : k7_enumset1(A_534,B_539,C_537,D_535,E_540,F_538,G_532,A_38,A_38) = k2_xboole_0(k5_enumset1(A_534,B_539,C_537,D_535,E_540,F_538,G_532),k1_tarski(A_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_2129])).

tff(c_10986,plain,(
    ! [B_1838,A_1836,F_1839,G_1837,C_1835,E_1840,D_1834,A_1833] : k7_enumset1(A_1836,B_1838,C_1835,D_1834,E_1840,F_1839,G_1837,A_1833,A_1833) = k6_enumset1(A_1836,B_1838,C_1835,D_1834,E_1840,F_1839,G_1837,A_1833) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2146])).

tff(c_18,plain,(
    ! [B_5,D_7,A_4,G_10,E_8,K_16,F_9,I_12,H_11] : r2_hidden(K_16,k7_enumset1(A_4,B_5,K_16,D_7,E_8,F_9,G_10,H_11,I_12)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_11481,plain,(
    ! [B_1846,A_1847,G_1844,D_1842,E_1845,A_1841,C_1843,F_1848] : r2_hidden(C_1843,k6_enumset1(A_1841,B_1846,C_1843,D_1842,E_1845,F_1848,G_1844,A_1847)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10986,c_18])).

tff(c_11546,plain,(
    ! [A_1851,C_1849,D_1854,G_1850,B_1852,E_1855,F_1853] : r2_hidden(B_1852,k5_enumset1(A_1851,B_1852,C_1849,D_1854,E_1855,F_1853,G_1850)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_11481])).

tff(c_11611,plain,(
    ! [E_1858,C_1856,B_1860,A_1857,D_1859,F_1861] : r2_hidden(A_1857,k4_enumset1(A_1857,B_1860,C_1856,D_1859,E_1858,F_1861)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_11546])).

tff(c_11696,plain,(
    ! [B_1869,D_1868,C_1871,A_1870,E_1872] : r2_hidden(A_1870,k3_enumset1(A_1870,B_1869,C_1871,D_1868,E_1872)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_11611])).

tff(c_11796,plain,(
    ! [H_1873,B_1874,H_1875] : r2_hidden(H_1873,k1_enumset1(H_1873,B_1874,H_1875)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8192,c_11696])).

tff(c_11942,plain,(
    ! [A_1877,B_1878] : r2_hidden(A_1877,k2_tarski(A_1877,B_1878)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_11796])).

tff(c_86,plain,(
    ! [A_68,B_69] : k3_tarski(k2_tarski(A_68,B_69)) = k2_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_127,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(A_78,k3_tarski(B_79))
      | ~ r2_hidden(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_130,plain,(
    ! [A_78,A_68,B_69] :
      ( r1_tarski(A_78,k2_xboole_0(A_68,B_69))
      | ~ r2_hidden(A_78,k2_tarski(A_68,B_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_127])).

tff(c_12604,plain,(
    ! [A_1889,B_1890] : r1_tarski(A_1889,k2_xboole_0(A_1889,B_1890)) ),
    inference(resolution,[status(thm)],[c_11942,c_130])).

tff(c_96,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_185,plain,(
    ! [A_94,C_95,B_96] :
      ( r1_tarski(A_94,C_95)
      | ~ r1_tarski(B_96,C_95)
      | ~ r1_tarski(A_94,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_191,plain,(
    ! [A_94] :
      ( r1_tarski(A_94,'#skF_5')
      | ~ r1_tarski(A_94,k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_96,c_185])).

tff(c_12696,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_12604,c_191])).

tff(c_92,plain,(
    ! [A_70,C_72,B_71] :
      ( r2_hidden(A_70,C_72)
      | ~ r1_tarski(k2_tarski(A_70,B_71),C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12742,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_12696,c_92])).

tff(c_12749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_12742])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:27:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.21/4.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.21/4.13  
% 11.21/4.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.21/4.13  %$ r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 11.21/4.13  
% 11.21/4.13  %Foreground sorts:
% 11.21/4.13  
% 11.21/4.13  
% 11.21/4.13  %Background operators:
% 11.21/4.13  
% 11.21/4.13  
% 11.21/4.13  %Foreground operators:
% 11.21/4.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.21/4.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.21/4.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.21/4.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.21/4.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.21/4.13  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.21/4.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.21/4.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.21/4.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.21/4.13  tff('#skF_5', type, '#skF_5': $i).
% 11.21/4.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.21/4.13  tff('#skF_3', type, '#skF_3': $i).
% 11.21/4.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.21/4.13  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.21/4.13  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.21/4.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.21/4.13  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.21/4.13  tff('#skF_4', type, '#skF_4': $i).
% 11.21/4.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.21/4.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.21/4.13  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.21/4.13  
% 11.21/4.15  tff(f_101, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 11.21/4.15  tff(f_74, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 11.21/4.15  tff(f_76, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 11.21/4.15  tff(f_78, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 11.21/4.15  tff(f_80, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 11.21/4.15  tff(f_82, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 11.21/4.15  tff(f_84, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 11.21/4.15  tff(f_70, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 11.21/4.15  tff(f_66, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 11.21/4.15  tff(f_72, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 11.21/4.15  tff(f_68, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k2_tarski(H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_enumset1)).
% 11.21/4.15  tff(f_64, axiom, (![A, B, C, D, E, F, G, H, I, J]: ((J = k7_enumset1(A, B, C, D, E, F, G, H, I)) <=> (![K]: (r2_hidden(K, J) <=> ~((((((((~(K = A) & ~(K = B)) & ~(K = C)) & ~(K = D)) & ~(K = E)) & ~(K = F)) & ~(K = G)) & ~(K = H)) & ~(K = I)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_enumset1)).
% 11.21/4.15  tff(f_90, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 11.21/4.15  tff(f_88, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 11.21/4.15  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.21/4.15  tff(f_96, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 11.21/4.15  tff(c_94, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.21/4.15  tff(c_72, plain, (![A_39, B_40]: (k1_enumset1(A_39, A_39, B_40)=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.21/4.15  tff(c_74, plain, (![A_41, B_42, C_43]: (k2_enumset1(A_41, A_41, B_42, C_43)=k1_enumset1(A_41, B_42, C_43))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.21/4.15  tff(c_76, plain, (![A_44, B_45, C_46, D_47]: (k3_enumset1(A_44, A_44, B_45, C_46, D_47)=k2_enumset1(A_44, B_45, C_46, D_47))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.21/4.15  tff(c_78, plain, (![B_49, A_48, D_51, E_52, C_50]: (k4_enumset1(A_48, A_48, B_49, C_50, D_51, E_52)=k3_enumset1(A_48, B_49, C_50, D_51, E_52))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.21/4.15  tff(c_80, plain, (![A_53, D_56, E_57, C_55, F_58, B_54]: (k5_enumset1(A_53, A_53, B_54, C_55, D_56, E_57, F_58)=k4_enumset1(A_53, B_54, C_55, D_56, E_57, F_58))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.21/4.15  tff(c_82, plain, (![F_64, D_62, A_59, G_65, C_61, E_63, B_60]: (k6_enumset1(A_59, A_59, B_60, C_61, D_62, E_63, F_64, G_65)=k5_enumset1(A_59, B_60, C_61, D_62, E_63, F_64, G_65))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.21/4.15  tff(c_1689, plain, (![G_455, B_450, E_453, D_454, A_452, F_451, H_448, C_449]: (k2_xboole_0(k5_enumset1(A_452, B_450, C_449, D_454, E_453, F_451, G_455), k1_tarski(H_448))=k6_enumset1(A_452, B_450, C_449, D_454, E_453, F_451, G_455, H_448))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.21/4.15  tff(c_1703, plain, (![A_53, D_56, E_57, C_55, F_58, H_448, B_54]: (k6_enumset1(A_53, A_53, B_54, C_55, D_56, E_57, F_58, H_448)=k2_xboole_0(k4_enumset1(A_53, B_54, C_55, D_56, E_57, F_58), k1_tarski(H_448)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_1689])).
% 11.21/4.15  tff(c_7736, plain, (![D_1626, B_1627, A_1623, H_1624, C_1622, E_1625, F_1628]: (k2_xboole_0(k4_enumset1(A_1623, B_1627, C_1622, D_1626, E_1625, F_1628), k1_tarski(H_1624))=k5_enumset1(A_1623, B_1627, C_1622, D_1626, E_1625, F_1628, H_1624))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1703])).
% 11.21/4.15  tff(c_7752, plain, (![B_49, A_48, D_51, E_52, C_50, H_1624]: (k5_enumset1(A_48, A_48, B_49, C_50, D_51, E_52, H_1624)=k2_xboole_0(k3_enumset1(A_48, B_49, C_50, D_51, E_52), k1_tarski(H_1624)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_7736])).
% 11.21/4.15  tff(c_7756, plain, (![D_1629, A_1631, E_1633, H_1634, C_1632, B_1630]: (k2_xboole_0(k3_enumset1(A_1631, B_1630, C_1632, D_1629, E_1633), k1_tarski(H_1634))=k4_enumset1(A_1631, B_1630, C_1632, D_1629, E_1633, H_1634))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_7752])).
% 11.21/4.15  tff(c_7772, plain, (![C_46, H_1634, A_44, B_45, D_47]: (k4_enumset1(A_44, A_44, B_45, C_46, D_47, H_1634)=k2_xboole_0(k2_enumset1(A_44, B_45, C_46, D_47), k1_tarski(H_1634)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_7756])).
% 11.21/4.15  tff(c_7776, plain, (![B_1638, A_1639, C_1637, H_1635, D_1636]: (k2_xboole_0(k2_enumset1(A_1639, B_1638, C_1637, D_1636), k1_tarski(H_1635))=k3_enumset1(A_1639, B_1638, C_1637, D_1636, H_1635))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_7772])).
% 11.21/4.15  tff(c_7801, plain, (![A_41, B_42, C_43, H_1635]: (k3_enumset1(A_41, A_41, B_42, C_43, H_1635)=k2_xboole_0(k1_enumset1(A_41, B_42, C_43), k1_tarski(H_1635)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_7776])).
% 11.21/4.15  tff(c_7806, plain, (![A_1650, B_1651, C_1652, H_1653]: (k2_xboole_0(k1_enumset1(A_1650, B_1651, C_1652), k1_tarski(H_1653))=k2_enumset1(A_1650, B_1651, C_1652, H_1653))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_7801])).
% 11.21/4.15  tff(c_7828, plain, (![A_39, B_40, H_1653]: (k2_xboole_0(k2_tarski(A_39, B_40), k1_tarski(H_1653))=k2_enumset1(A_39, A_39, B_40, H_1653))), inference(superposition, [status(thm), theory('equality')], [c_72, c_7806])).
% 11.21/4.15  tff(c_7831, plain, (![A_39, B_40, H_1653]: (k2_xboole_0(k2_tarski(A_39, B_40), k1_tarski(H_1653))=k1_enumset1(A_39, B_40, H_1653))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_7828])).
% 11.21/4.15  tff(c_200, plain, (![D_103, C_104, B_105, A_106]: (k2_enumset1(D_103, C_104, B_105, A_106)=k2_enumset1(A_106, B_105, C_104, D_103))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.21/4.15  tff(c_247, plain, (![D_107, C_108, B_109]: (k2_enumset1(D_107, C_108, B_109, B_109)=k1_enumset1(B_109, C_108, D_107))), inference(superposition, [status(thm), theory('equality')], [c_200, c_74])).
% 11.21/4.15  tff(c_260, plain, (![C_108, B_109]: (k1_enumset1(C_108, B_109, B_109)=k1_enumset1(B_109, C_108, C_108))), inference(superposition, [status(thm), theory('equality')], [c_247, c_74])).
% 11.21/4.15  tff(c_7968, plain, (![C_1664, B_1665, H_1666]: (k2_xboole_0(k1_enumset1(C_1664, B_1665, B_1665), k1_tarski(H_1666))=k2_enumset1(B_1665, C_1664, C_1664, H_1666))), inference(superposition, [status(thm), theory('equality')], [c_260, c_7806])).
% 11.21/4.15  tff(c_7804, plain, (![A_41, B_42, C_43, H_1635]: (k2_xboole_0(k1_enumset1(A_41, B_42, C_43), k1_tarski(H_1635))=k2_enumset1(A_41, B_42, C_43, H_1635))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_7801])).
% 11.21/4.15  tff(c_8040, plain, (![C_1667, B_1668, H_1669]: (k2_enumset1(C_1667, B_1668, B_1668, H_1669)=k2_enumset1(B_1668, C_1667, C_1667, H_1669))), inference(superposition, [status(thm), theory('equality')], [c_7968, c_7804])).
% 11.21/4.15  tff(c_216, plain, (![D_103, C_104, B_105]: (k2_enumset1(D_103, C_104, B_105, B_105)=k1_enumset1(B_105, C_104, D_103))), inference(superposition, [status(thm), theory('equality')], [c_200, c_74])).
% 11.21/4.15  tff(c_8068, plain, (![H_1669, B_1668]: (k2_enumset1(H_1669, B_1668, B_1668, H_1669)=k1_enumset1(H_1669, H_1669, B_1668))), inference(superposition, [status(thm), theory('equality')], [c_8040, c_216])).
% 11.21/4.15  tff(c_8144, plain, (![H_1680, B_1681]: (k2_enumset1(H_1680, B_1681, B_1681, H_1680)=k2_tarski(H_1680, B_1681))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_8068])).
% 11.21/4.15  tff(c_7775, plain, (![C_46, H_1634, A_44, B_45, D_47]: (k2_xboole_0(k2_enumset1(A_44, B_45, C_46, D_47), k1_tarski(H_1634))=k3_enumset1(A_44, B_45, C_46, D_47, H_1634))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_7772])).
% 11.21/4.15  tff(c_8159, plain, (![H_1680, B_1681, H_1634]: (k3_enumset1(H_1680, B_1681, B_1681, H_1680, H_1634)=k2_xboole_0(k2_tarski(H_1680, B_1681), k1_tarski(H_1634)))), inference(superposition, [status(thm), theory('equality')], [c_8144, c_7775])).
% 11.21/4.15  tff(c_8192, plain, (![H_1680, B_1681, H_1634]: (k3_enumset1(H_1680, B_1681, B_1681, H_1680, H_1634)=k1_enumset1(H_1680, B_1681, H_1634))), inference(demodulation, [status(thm), theory('equality')], [c_7831, c_8159])).
% 11.21/4.15  tff(c_68, plain, (![D_33, A_30, C_32, H_37, B_31, E_34, G_36, F_35]: (k2_xboole_0(k5_enumset1(A_30, B_31, C_32, D_33, E_34, F_35, G_36), k1_tarski(H_37))=k6_enumset1(A_30, B_31, C_32, D_33, E_34, F_35, G_36, H_37))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.21/4.15  tff(c_70, plain, (![A_38]: (k2_tarski(A_38, A_38)=k1_tarski(A_38))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.21/4.15  tff(c_2129, plain, (![G_532, F_538, E_540, H_536, D_535, I_533, C_537, A_534, B_539]: (k2_xboole_0(k5_enumset1(A_534, B_539, C_537, D_535, E_540, F_538, G_532), k2_tarski(H_536, I_533))=k7_enumset1(A_534, B_539, C_537, D_535, E_540, F_538, G_532, H_536, I_533))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.21/4.15  tff(c_2146, plain, (![G_532, F_538, E_540, D_535, C_537, A_534, A_38, B_539]: (k7_enumset1(A_534, B_539, C_537, D_535, E_540, F_538, G_532, A_38, A_38)=k2_xboole_0(k5_enumset1(A_534, B_539, C_537, D_535, E_540, F_538, G_532), k1_tarski(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_2129])).
% 11.21/4.15  tff(c_10986, plain, (![B_1838, A_1836, F_1839, G_1837, C_1835, E_1840, D_1834, A_1833]: (k7_enumset1(A_1836, B_1838, C_1835, D_1834, E_1840, F_1839, G_1837, A_1833, A_1833)=k6_enumset1(A_1836, B_1838, C_1835, D_1834, E_1840, F_1839, G_1837, A_1833))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2146])).
% 11.21/4.15  tff(c_18, plain, (![B_5, D_7, A_4, G_10, E_8, K_16, F_9, I_12, H_11]: (r2_hidden(K_16, k7_enumset1(A_4, B_5, K_16, D_7, E_8, F_9, G_10, H_11, I_12)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.21/4.15  tff(c_11481, plain, (![B_1846, A_1847, G_1844, D_1842, E_1845, A_1841, C_1843, F_1848]: (r2_hidden(C_1843, k6_enumset1(A_1841, B_1846, C_1843, D_1842, E_1845, F_1848, G_1844, A_1847)))), inference(superposition, [status(thm), theory('equality')], [c_10986, c_18])).
% 11.21/4.15  tff(c_11546, plain, (![A_1851, C_1849, D_1854, G_1850, B_1852, E_1855, F_1853]: (r2_hidden(B_1852, k5_enumset1(A_1851, B_1852, C_1849, D_1854, E_1855, F_1853, G_1850)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_11481])).
% 11.21/4.15  tff(c_11611, plain, (![E_1858, C_1856, B_1860, A_1857, D_1859, F_1861]: (r2_hidden(A_1857, k4_enumset1(A_1857, B_1860, C_1856, D_1859, E_1858, F_1861)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_11546])).
% 11.21/4.15  tff(c_11696, plain, (![B_1869, D_1868, C_1871, A_1870, E_1872]: (r2_hidden(A_1870, k3_enumset1(A_1870, B_1869, C_1871, D_1868, E_1872)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_11611])).
% 11.21/4.15  tff(c_11796, plain, (![H_1873, B_1874, H_1875]: (r2_hidden(H_1873, k1_enumset1(H_1873, B_1874, H_1875)))), inference(superposition, [status(thm), theory('equality')], [c_8192, c_11696])).
% 11.21/4.15  tff(c_11942, plain, (![A_1877, B_1878]: (r2_hidden(A_1877, k2_tarski(A_1877, B_1878)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_11796])).
% 11.21/4.15  tff(c_86, plain, (![A_68, B_69]: (k3_tarski(k2_tarski(A_68, B_69))=k2_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.15  tff(c_127, plain, (![A_78, B_79]: (r1_tarski(A_78, k3_tarski(B_79)) | ~r2_hidden(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.21/4.15  tff(c_130, plain, (![A_78, A_68, B_69]: (r1_tarski(A_78, k2_xboole_0(A_68, B_69)) | ~r2_hidden(A_78, k2_tarski(A_68, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_127])).
% 11.21/4.15  tff(c_12604, plain, (![A_1889, B_1890]: (r1_tarski(A_1889, k2_xboole_0(A_1889, B_1890)))), inference(resolution, [status(thm)], [c_11942, c_130])).
% 11.21/4.15  tff(c_96, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.21/4.15  tff(c_185, plain, (![A_94, C_95, B_96]: (r1_tarski(A_94, C_95) | ~r1_tarski(B_96, C_95) | ~r1_tarski(A_94, B_96))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.21/4.15  tff(c_191, plain, (![A_94]: (r1_tarski(A_94, '#skF_5') | ~r1_tarski(A_94, k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')))), inference(resolution, [status(thm)], [c_96, c_185])).
% 11.21/4.15  tff(c_12696, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_12604, c_191])).
% 11.21/4.15  tff(c_92, plain, (![A_70, C_72, B_71]: (r2_hidden(A_70, C_72) | ~r1_tarski(k2_tarski(A_70, B_71), C_72))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.21/4.15  tff(c_12742, plain, (r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_12696, c_92])).
% 11.21/4.15  tff(c_12749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_12742])).
% 11.21/4.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.21/4.15  
% 11.21/4.15  Inference rules
% 11.21/4.15  ----------------------
% 11.21/4.15  #Ref     : 0
% 11.21/4.15  #Sup     : 3225
% 11.21/4.15  #Fact    : 0
% 11.21/4.15  #Define  : 0
% 11.21/4.15  #Split   : 0
% 11.21/4.15  #Chain   : 0
% 11.21/4.15  #Close   : 0
% 11.21/4.15  
% 11.21/4.15  Ordering : KBO
% 11.21/4.15  
% 11.21/4.15  Simplification rules
% 11.21/4.15  ----------------------
% 11.21/4.15  #Subsume      : 196
% 11.21/4.15  #Demod        : 492
% 11.21/4.15  #Tautology    : 460
% 11.21/4.15  #SimpNegUnit  : 1
% 11.21/4.15  #BackRed      : 0
% 11.21/4.15  
% 11.21/4.15  #Partial instantiations: 0
% 11.21/4.15  #Strategies tried      : 1
% 11.21/4.15  
% 11.21/4.15  Timing (in seconds)
% 11.21/4.15  ----------------------
% 11.21/4.16  Preprocessing        : 0.44
% 11.21/4.16  Parsing              : 0.21
% 11.21/4.16  CNF conversion       : 0.03
% 11.21/4.16  Main loop            : 2.92
% 11.21/4.16  Inferencing          : 0.69
% 11.21/4.16  Reduction            : 1.02
% 11.21/4.16  Demodulation         : 0.82
% 11.21/4.16  BG Simplification    : 0.09
% 11.21/4.16  Subsumption          : 0.95
% 11.21/4.16  Abstraction          : 0.14
% 11.21/4.16  MUC search           : 0.00
% 11.21/4.16  Cooper               : 0.00
% 11.21/4.16  Total                : 3.40
% 11.21/4.16  Index Insertion      : 0.00
% 11.21/4.16  Index Deletion       : 0.00
% 11.21/4.16  Index Matching       : 0.00
% 11.21/4.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
