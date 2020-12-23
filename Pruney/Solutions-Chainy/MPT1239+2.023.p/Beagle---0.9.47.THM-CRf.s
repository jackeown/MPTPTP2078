%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:44 EST 2020

% Result     : Theorem 44.45s
% Output     : CNFRefutation 44.45s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 313 expanded)
%              Number of leaves         :   28 ( 116 expanded)
%              Depth                    :   20
%              Number of atoms          :  206 ( 671 expanded)
%              Number of equality atoms :   21 (  42 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k1_tops_1(A,k7_subset_1(u1_struct_0(A),B,C)),k7_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_55,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_44])).

tff(c_91,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_tarski(A_56,C_57)
      | ~ r1_tarski(B_58,C_57)
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    ! [A_56] :
      ( r1_tarski(A_56,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_56,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_55,c_91])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_565,plain,(
    ! [A_115,C_116,B_117,D_118] :
      ( r1_xboole_0(A_115,C_116)
      | ~ r1_xboole_0(B_117,D_118)
      | ~ r1_tarski(C_116,D_118)
      | ~ r1_tarski(A_115,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_575,plain,(
    ! [A_119,C_120,B_121,A_122] :
      ( r1_xboole_0(A_119,C_120)
      | ~ r1_tarski(C_120,B_121)
      | ~ r1_tarski(A_119,k4_xboole_0(A_122,B_121)) ) ),
    inference(resolution,[status(thm)],[c_16,c_565])).

tff(c_743,plain,(
    ! [A_133,A_134,B_135,A_136] :
      ( r1_xboole_0(A_133,k4_xboole_0(A_134,B_135))
      | ~ r1_tarski(A_133,k4_xboole_0(A_136,A_134)) ) ),
    inference(resolution,[status(thm)],[c_10,c_575])).

tff(c_764,plain,(
    ! [A_136,A_134,B_135] : r1_xboole_0(k4_xboole_0(A_136,A_134),k4_xboole_0(A_134,B_135)) ),
    inference(resolution,[status(thm)],[c_6,c_743])).

tff(c_122,plain,(
    ! [A_64,A_65,B_66] :
      ( r1_tarski(A_64,A_65)
      | ~ r1_tarski(A_64,k4_xboole_0(A_65,B_66)) ) ),
    inference(resolution,[status(thm)],[c_10,c_91])).

tff(c_131,plain,(
    ! [A_65,B_66,B_7] : r1_tarski(k4_xboole_0(k4_xboole_0(A_65,B_66),B_7),A_65) ),
    inference(resolution,[status(thm)],[c_10,c_122])).

tff(c_18,plain,(
    ! [A_17,B_18,C_19] :
      ( r1_tarski(A_17,k4_xboole_0(B_18,C_19))
      | ~ r1_xboole_0(A_17,C_19)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_254,plain,(
    ! [A_91,B_92,C_93] :
      ( r1_tarski(A_91,k4_xboole_0(B_92,C_93))
      | ~ r1_xboole_0(A_91,C_93)
      | ~ r1_tarski(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1382,plain,(
    ! [A_173,B_174,C_175,A_176] :
      ( r1_tarski(A_173,k4_xboole_0(B_174,C_175))
      | ~ r1_tarski(A_173,A_176)
      | ~ r1_xboole_0(A_176,C_175)
      | ~ r1_tarski(A_176,B_174) ) ),
    inference(resolution,[status(thm)],[c_254,c_8])).

tff(c_10304,plain,(
    ! [A_465,C_464,B_467,C_463,B_466] :
      ( r1_tarski(A_465,k4_xboole_0(B_467,C_464))
      | ~ r1_xboole_0(k4_xboole_0(B_466,C_463),C_464)
      | ~ r1_tarski(k4_xboole_0(B_466,C_463),B_467)
      | ~ r1_xboole_0(A_465,C_463)
      | ~ r1_tarski(A_465,B_466) ) ),
    inference(resolution,[status(thm)],[c_18,c_1382])).

tff(c_44779,plain,(
    ! [A_983,B_984,B_985,A_986] :
      ( r1_tarski(A_983,k4_xboole_0(B_984,B_985))
      | ~ r1_tarski(k4_xboole_0(A_986,B_985),B_984)
      | ~ r1_xboole_0(A_983,B_985)
      | ~ r1_tarski(A_983,A_986) ) ),
    inference(resolution,[status(thm)],[c_16,c_10304])).

tff(c_45363,plain,(
    ! [A_991,A_992,B_993,B_994] :
      ( r1_tarski(A_991,k4_xboole_0(A_992,B_993))
      | ~ r1_xboole_0(A_991,B_993)
      | ~ r1_tarski(A_991,k4_xboole_0(A_992,B_994)) ) ),
    inference(resolution,[status(thm)],[c_131,c_44779])).

tff(c_45469,plain,(
    ! [A_992,B_994,B_993] :
      ( r1_tarski(k4_xboole_0(A_992,B_994),k4_xboole_0(A_992,B_993))
      | ~ r1_xboole_0(k4_xboole_0(A_992,B_994),B_993) ) ),
    inference(resolution,[status(thm)],[c_6,c_45363])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1758,plain,(
    ! [B_195,C_196,A_197] :
      ( k4_xboole_0(B_195,C_196) = A_197
      | ~ r1_tarski(k4_xboole_0(B_195,C_196),A_197)
      | ~ r1_xboole_0(A_197,C_196)
      | ~ r1_tarski(A_197,B_195) ) ),
    inference(resolution,[status(thm)],[c_254,c_2])).

tff(c_11818,plain,(
    ! [B_515,C_516,B_513,C_514] :
      ( k4_xboole_0(B_515,C_516) = k4_xboole_0(B_513,C_514)
      | ~ r1_xboole_0(k4_xboole_0(B_515,C_516),C_514)
      | ~ r1_tarski(k4_xboole_0(B_515,C_516),B_513)
      | ~ r1_xboole_0(k4_xboole_0(B_513,C_514),C_516)
      | ~ r1_tarski(k4_xboole_0(B_513,C_514),B_515) ) ),
    inference(resolution,[status(thm)],[c_18,c_1758])).

tff(c_11962,plain,(
    ! [B_513,B_16,A_15] :
      ( k4_xboole_0(B_513,B_16) = k4_xboole_0(A_15,B_16)
      | ~ r1_tarski(k4_xboole_0(A_15,B_16),B_513)
      | ~ r1_xboole_0(k4_xboole_0(B_513,B_16),B_16)
      | ~ r1_tarski(k4_xboole_0(B_513,B_16),A_15) ) ),
    inference(resolution,[status(thm)],[c_16,c_11818])).

tff(c_51031,plain,(
    ! [B_1058,B_1059,A_1060] :
      ( k4_xboole_0(B_1058,B_1059) = k4_xboole_0(A_1060,B_1059)
      | ~ r1_tarski(k4_xboole_0(A_1060,B_1059),B_1058)
      | ~ r1_tarski(k4_xboole_0(B_1058,B_1059),A_1060) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_11962])).

tff(c_51037,plain,(
    ! [A_992,B_993,B_994] :
      ( k4_xboole_0(k4_xboole_0(A_992,B_993),B_994) = k4_xboole_0(A_992,B_994)
      | ~ r1_tarski(k4_xboole_0(k4_xboole_0(A_992,B_993),B_994),A_992)
      | ~ r1_xboole_0(k4_xboole_0(A_992,B_994),B_993) ) ),
    inference(resolution,[status(thm)],[c_45469,c_51031])).

tff(c_62717,plain,(
    ! [A_1212,B_1213,B_1214] :
      ( k4_xboole_0(k4_xboole_0(A_1212,B_1213),B_1214) = k4_xboole_0(A_1212,B_1214)
      | ~ r1_xboole_0(k4_xboole_0(A_1212,B_1214),B_1213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_51037])).

tff(c_68432,plain,(
    ! [A_1223,A_1224,B_1225] : k4_xboole_0(k4_xboole_0(A_1223,k4_xboole_0(A_1224,B_1225)),A_1224) = k4_xboole_0(A_1223,A_1224) ),
    inference(resolution,[status(thm)],[c_764,c_62717])).

tff(c_3218,plain,(
    ! [A_257,B_258,B_259,C_260] :
      ( r1_tarski(k4_xboole_0(A_257,B_258),k4_xboole_0(B_259,C_260))
      | ~ r1_xboole_0(A_257,C_260)
      | ~ r1_tarski(A_257,B_259) ) ),
    inference(resolution,[status(thm)],[c_10,c_1382])).

tff(c_102,plain,(
    ! [A_56,A_6,B_7] :
      ( r1_tarski(A_56,A_6)
      | ~ r1_tarski(A_56,k4_xboole_0(A_6,B_7)) ) ),
    inference(resolution,[status(thm)],[c_10,c_91])).

tff(c_5016,plain,(
    ! [A_320,B_321,B_322,C_323] :
      ( r1_tarski(k4_xboole_0(A_320,B_321),B_322)
      | ~ r1_xboole_0(A_320,C_323)
      | ~ r1_tarski(A_320,B_322) ) ),
    inference(resolution,[status(thm)],[c_3218,c_102])).

tff(c_5117,plain,(
    ! [A_136,A_134,B_321,B_322] :
      ( r1_tarski(k4_xboole_0(k4_xboole_0(A_136,A_134),B_321),B_322)
      | ~ r1_tarski(k4_xboole_0(A_136,A_134),B_322) ) ),
    inference(resolution,[status(thm)],[c_764,c_5016])).

tff(c_110929,plain,(
    ! [A_1385,A_1386,B_1387,B_1388] :
      ( r1_tarski(k4_xboole_0(A_1385,A_1386),B_1387)
      | ~ r1_tarski(k4_xboole_0(A_1385,k4_xboole_0(A_1386,B_1388)),B_1387) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68432,c_5117])).

tff(c_114836,plain,(
    ! [A_1414,A_1415,B_1416] :
      ( r1_tarski(k4_xboole_0(A_1414,A_1415),u1_struct_0('#skF_1'))
      | ~ r1_tarski(k4_xboole_0(A_1414,k4_xboole_0(A_1415,B_1416)),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_101,c_110929])).

tff(c_115101,plain,(
    ! [A_1415] : r1_tarski(k4_xboole_0('#skF_2',A_1415),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_114836])).

tff(c_24,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_28,plain,(
    ! [A_28,B_32,C_34] :
      ( r1_tarski(k1_tops_1(A_28,B_32),k1_tops_1(A_28,C_34))
      | ~ r1_tarski(B_32,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_784,plain,(
    ! [A_140,B_141] :
      ( r1_tarski(k1_tops_1(A_140,B_141),B_141)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1118,plain,(
    ! [A_159,A_160] :
      ( r1_tarski(k1_tops_1(A_159,A_160),A_160)
      | ~ l1_pre_topc(A_159)
      | ~ r1_tarski(A_160,u1_struct_0(A_159)) ) ),
    inference(resolution,[status(thm)],[c_24,c_784])).

tff(c_74,plain,(
    ! [A_50,C_51,B_52] :
      ( r1_xboole_0(A_50,C_51)
      | ~ r1_xboole_0(B_52,C_51)
      | ~ r1_tarski(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_77,plain,(
    ! [A_50,B_16,A_15] :
      ( r1_xboole_0(A_50,B_16)
      | ~ r1_tarski(A_50,k4_xboole_0(A_15,B_16)) ) ),
    inference(resolution,[status(thm)],[c_16,c_74])).

tff(c_5459,plain,(
    ! [A_337,A_338,B_339] :
      ( r1_xboole_0(k1_tops_1(A_337,k4_xboole_0(A_338,B_339)),B_339)
      | ~ l1_pre_topc(A_337)
      | ~ r1_tarski(k4_xboole_0(A_338,B_339),u1_struct_0(A_337)) ) ),
    inference(resolution,[status(thm)],[c_1118,c_77])).

tff(c_57,plain,(
    ! [B_48,A_49] :
      ( B_48 = A_49
      | ~ r1_tarski(B_48,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,k4_xboole_0(A_6,B_7)) ) ),
    inference(resolution,[status(thm)],[c_10,c_57])).

tff(c_264,plain,(
    ! [B_92,C_93] :
      ( k4_xboole_0(B_92,C_93) = B_92
      | ~ r1_xboole_0(B_92,C_93)
      | ~ r1_tarski(B_92,B_92) ) ),
    inference(resolution,[status(thm)],[c_254,c_68])).

tff(c_279,plain,(
    ! [B_92,C_93] :
      ( k4_xboole_0(B_92,C_93) = B_92
      | ~ r1_xboole_0(B_92,C_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_264])).

tff(c_159692,plain,(
    ! [A_1657,A_1658,B_1659] :
      ( k4_xboole_0(k1_tops_1(A_1657,k4_xboole_0(A_1658,B_1659)),B_1659) = k1_tops_1(A_1657,k4_xboole_0(A_1658,B_1659))
      | ~ l1_pre_topc(A_1657)
      | ~ r1_tarski(k4_xboole_0(A_1658,B_1659),u1_struct_0(A_1657)) ) ),
    inference(resolution,[status(thm)],[c_5459,c_279])).

tff(c_159710,plain,(
    ! [A_1415] :
      ( k4_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',A_1415)),A_1415) = k1_tops_1('#skF_1',k4_xboole_0('#skF_2',A_1415))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_115101,c_159692])).

tff(c_161573,plain,(
    ! [A_1676] : k4_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',A_1676)),A_1676) = k1_tops_1('#skF_1',k4_xboole_0('#skF_2',A_1676)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_159710])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_791,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_784])).

tff(c_798,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_791])).

tff(c_574,plain,(
    ! [A_115,C_116,B_16,A_15] :
      ( r1_xboole_0(A_115,C_116)
      | ~ r1_tarski(C_116,B_16)
      | ~ r1_tarski(A_115,k4_xboole_0(A_15,B_16)) ) ),
    inference(resolution,[status(thm)],[c_16,c_565])).

tff(c_1252,plain,(
    ! [A_163,A_164] :
      ( r1_xboole_0(A_163,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_163,k4_xboole_0(A_164,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_798,c_574])).

tff(c_1279,plain,(
    ! [A_164] : r1_xboole_0(k4_xboole_0(A_164,'#skF_3'),k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_1252])).

tff(c_163264,plain,(
    r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_161573,c_1279])).

tff(c_789,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_784])).

tff(c_795,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_789])).

tff(c_115,plain,(
    ! [A_63] :
      ( r1_tarski(A_63,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_63,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_55,c_91])).

tff(c_120,plain,(
    ! [A_3,A_63] :
      ( r1_tarski(A_3,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_3,A_63)
      | ~ r1_tarski(A_63,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_115,c_8])).

tff(c_804,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_795,c_120])).

tff(c_815,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_804])).

tff(c_151,plain,(
    ! [A_70,B_71,C_72] :
      ( k7_subset_1(A_70,B_71,C_72) = k4_xboole_0(B_71,C_72)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_158,plain,(
    ! [B_24,A_23,C_72] :
      ( k7_subset_1(B_24,A_23,C_72) = k4_xboole_0(A_23,C_72)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_24,c_151])).

tff(c_856,plain,(
    ! [C_72] : k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_72) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_72) ),
    inference(resolution,[status(thm)],[c_815,c_158])).

tff(c_159,plain,(
    ! [C_72] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_72) = k4_xboole_0('#skF_2',C_72) ),
    inference(resolution,[status(thm)],[c_34,c_151])).

tff(c_30,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_161,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_30])).

tff(c_18559,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_161])).

tff(c_18798,plain,
    ( ~ r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_18559])).

tff(c_172474,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163264,c_18798])).

tff(c_172477,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k4_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_172474])).

tff(c_172480,plain,(
    ~ m1_subset_1(k4_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_10,c_172477])).

tff(c_172483,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_172480])).

tff(c_172487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115101,c_172483])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:09:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 44.45/34.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 44.45/34.84  
% 44.45/34.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 44.45/34.84  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 44.45/34.84  
% 44.45/34.84  %Foreground sorts:
% 44.45/34.84  
% 44.45/34.84  
% 44.45/34.84  %Background operators:
% 44.45/34.84  
% 44.45/34.84  
% 44.45/34.84  %Foreground operators:
% 44.45/34.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 44.45/34.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 44.45/34.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 44.45/34.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 44.45/34.84  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 44.45/34.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 44.45/34.84  tff('#skF_2', type, '#skF_2': $i).
% 44.45/34.84  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 44.45/34.84  tff('#skF_3', type, '#skF_3': $i).
% 44.45/34.84  tff('#skF_1', type, '#skF_1': $i).
% 44.45/34.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 44.45/34.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 44.45/34.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 44.45/34.84  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 44.45/34.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 44.45/34.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 44.45/34.84  
% 44.45/34.86  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 44.45/34.86  tff(f_101, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, k7_subset_1(u1_struct_0(A), B, C)), k7_subset_1(u1_struct_0(A), k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tops_1)).
% 44.45/34.86  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 44.45/34.86  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 44.45/34.86  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 44.45/34.86  tff(f_55, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 44.45/34.86  tff(f_53, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 44.45/34.86  tff(f_61, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 44.45/34.86  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 44.45/34.86  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 44.45/34.86  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 44.45/34.86  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 44.45/34.86  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 44.45/34.86  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 44.45/34.86  tff(c_44, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 44.45/34.86  tff(c_55, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_44])).
% 44.45/34.86  tff(c_91, plain, (![A_56, C_57, B_58]: (r1_tarski(A_56, C_57) | ~r1_tarski(B_58, C_57) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 44.45/34.86  tff(c_101, plain, (![A_56]: (r1_tarski(A_56, u1_struct_0('#skF_1')) | ~r1_tarski(A_56, '#skF_2'))), inference(resolution, [status(thm)], [c_55, c_91])).
% 44.45/34.86  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 44.45/34.86  tff(c_16, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 44.45/34.86  tff(c_565, plain, (![A_115, C_116, B_117, D_118]: (r1_xboole_0(A_115, C_116) | ~r1_xboole_0(B_117, D_118) | ~r1_tarski(C_116, D_118) | ~r1_tarski(A_115, B_117))), inference(cnfTransformation, [status(thm)], [f_53])).
% 44.45/34.86  tff(c_575, plain, (![A_119, C_120, B_121, A_122]: (r1_xboole_0(A_119, C_120) | ~r1_tarski(C_120, B_121) | ~r1_tarski(A_119, k4_xboole_0(A_122, B_121)))), inference(resolution, [status(thm)], [c_16, c_565])).
% 44.45/34.86  tff(c_743, plain, (![A_133, A_134, B_135, A_136]: (r1_xboole_0(A_133, k4_xboole_0(A_134, B_135)) | ~r1_tarski(A_133, k4_xboole_0(A_136, A_134)))), inference(resolution, [status(thm)], [c_10, c_575])).
% 44.45/34.86  tff(c_764, plain, (![A_136, A_134, B_135]: (r1_xboole_0(k4_xboole_0(A_136, A_134), k4_xboole_0(A_134, B_135)))), inference(resolution, [status(thm)], [c_6, c_743])).
% 44.45/34.86  tff(c_122, plain, (![A_64, A_65, B_66]: (r1_tarski(A_64, A_65) | ~r1_tarski(A_64, k4_xboole_0(A_65, B_66)))), inference(resolution, [status(thm)], [c_10, c_91])).
% 44.45/34.86  tff(c_131, plain, (![A_65, B_66, B_7]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_65, B_66), B_7), A_65))), inference(resolution, [status(thm)], [c_10, c_122])).
% 44.45/34.86  tff(c_18, plain, (![A_17, B_18, C_19]: (r1_tarski(A_17, k4_xboole_0(B_18, C_19)) | ~r1_xboole_0(A_17, C_19) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 44.45/34.86  tff(c_254, plain, (![A_91, B_92, C_93]: (r1_tarski(A_91, k4_xboole_0(B_92, C_93)) | ~r1_xboole_0(A_91, C_93) | ~r1_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_61])).
% 44.45/34.86  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 44.45/34.86  tff(c_1382, plain, (![A_173, B_174, C_175, A_176]: (r1_tarski(A_173, k4_xboole_0(B_174, C_175)) | ~r1_tarski(A_173, A_176) | ~r1_xboole_0(A_176, C_175) | ~r1_tarski(A_176, B_174))), inference(resolution, [status(thm)], [c_254, c_8])).
% 44.45/34.86  tff(c_10304, plain, (![A_465, C_464, B_467, C_463, B_466]: (r1_tarski(A_465, k4_xboole_0(B_467, C_464)) | ~r1_xboole_0(k4_xboole_0(B_466, C_463), C_464) | ~r1_tarski(k4_xboole_0(B_466, C_463), B_467) | ~r1_xboole_0(A_465, C_463) | ~r1_tarski(A_465, B_466))), inference(resolution, [status(thm)], [c_18, c_1382])).
% 44.45/34.86  tff(c_44779, plain, (![A_983, B_984, B_985, A_986]: (r1_tarski(A_983, k4_xboole_0(B_984, B_985)) | ~r1_tarski(k4_xboole_0(A_986, B_985), B_984) | ~r1_xboole_0(A_983, B_985) | ~r1_tarski(A_983, A_986))), inference(resolution, [status(thm)], [c_16, c_10304])).
% 44.45/34.86  tff(c_45363, plain, (![A_991, A_992, B_993, B_994]: (r1_tarski(A_991, k4_xboole_0(A_992, B_993)) | ~r1_xboole_0(A_991, B_993) | ~r1_tarski(A_991, k4_xboole_0(A_992, B_994)))), inference(resolution, [status(thm)], [c_131, c_44779])).
% 44.45/34.86  tff(c_45469, plain, (![A_992, B_994, B_993]: (r1_tarski(k4_xboole_0(A_992, B_994), k4_xboole_0(A_992, B_993)) | ~r1_xboole_0(k4_xboole_0(A_992, B_994), B_993))), inference(resolution, [status(thm)], [c_6, c_45363])).
% 44.45/34.86  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 44.45/34.86  tff(c_1758, plain, (![B_195, C_196, A_197]: (k4_xboole_0(B_195, C_196)=A_197 | ~r1_tarski(k4_xboole_0(B_195, C_196), A_197) | ~r1_xboole_0(A_197, C_196) | ~r1_tarski(A_197, B_195))), inference(resolution, [status(thm)], [c_254, c_2])).
% 44.45/34.86  tff(c_11818, plain, (![B_515, C_516, B_513, C_514]: (k4_xboole_0(B_515, C_516)=k4_xboole_0(B_513, C_514) | ~r1_xboole_0(k4_xboole_0(B_515, C_516), C_514) | ~r1_tarski(k4_xboole_0(B_515, C_516), B_513) | ~r1_xboole_0(k4_xboole_0(B_513, C_514), C_516) | ~r1_tarski(k4_xboole_0(B_513, C_514), B_515))), inference(resolution, [status(thm)], [c_18, c_1758])).
% 44.45/34.86  tff(c_11962, plain, (![B_513, B_16, A_15]: (k4_xboole_0(B_513, B_16)=k4_xboole_0(A_15, B_16) | ~r1_tarski(k4_xboole_0(A_15, B_16), B_513) | ~r1_xboole_0(k4_xboole_0(B_513, B_16), B_16) | ~r1_tarski(k4_xboole_0(B_513, B_16), A_15))), inference(resolution, [status(thm)], [c_16, c_11818])).
% 44.45/34.86  tff(c_51031, plain, (![B_1058, B_1059, A_1060]: (k4_xboole_0(B_1058, B_1059)=k4_xboole_0(A_1060, B_1059) | ~r1_tarski(k4_xboole_0(A_1060, B_1059), B_1058) | ~r1_tarski(k4_xboole_0(B_1058, B_1059), A_1060))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_11962])).
% 44.45/34.86  tff(c_51037, plain, (![A_992, B_993, B_994]: (k4_xboole_0(k4_xboole_0(A_992, B_993), B_994)=k4_xboole_0(A_992, B_994) | ~r1_tarski(k4_xboole_0(k4_xboole_0(A_992, B_993), B_994), A_992) | ~r1_xboole_0(k4_xboole_0(A_992, B_994), B_993))), inference(resolution, [status(thm)], [c_45469, c_51031])).
% 44.45/34.86  tff(c_62717, plain, (![A_1212, B_1213, B_1214]: (k4_xboole_0(k4_xboole_0(A_1212, B_1213), B_1214)=k4_xboole_0(A_1212, B_1214) | ~r1_xboole_0(k4_xboole_0(A_1212, B_1214), B_1213))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_51037])).
% 44.45/34.86  tff(c_68432, plain, (![A_1223, A_1224, B_1225]: (k4_xboole_0(k4_xboole_0(A_1223, k4_xboole_0(A_1224, B_1225)), A_1224)=k4_xboole_0(A_1223, A_1224))), inference(resolution, [status(thm)], [c_764, c_62717])).
% 44.45/34.86  tff(c_3218, plain, (![A_257, B_258, B_259, C_260]: (r1_tarski(k4_xboole_0(A_257, B_258), k4_xboole_0(B_259, C_260)) | ~r1_xboole_0(A_257, C_260) | ~r1_tarski(A_257, B_259))), inference(resolution, [status(thm)], [c_10, c_1382])).
% 44.45/34.86  tff(c_102, plain, (![A_56, A_6, B_7]: (r1_tarski(A_56, A_6) | ~r1_tarski(A_56, k4_xboole_0(A_6, B_7)))), inference(resolution, [status(thm)], [c_10, c_91])).
% 44.45/34.86  tff(c_5016, plain, (![A_320, B_321, B_322, C_323]: (r1_tarski(k4_xboole_0(A_320, B_321), B_322) | ~r1_xboole_0(A_320, C_323) | ~r1_tarski(A_320, B_322))), inference(resolution, [status(thm)], [c_3218, c_102])).
% 44.45/34.86  tff(c_5117, plain, (![A_136, A_134, B_321, B_322]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_136, A_134), B_321), B_322) | ~r1_tarski(k4_xboole_0(A_136, A_134), B_322))), inference(resolution, [status(thm)], [c_764, c_5016])).
% 44.45/34.86  tff(c_110929, plain, (![A_1385, A_1386, B_1387, B_1388]: (r1_tarski(k4_xboole_0(A_1385, A_1386), B_1387) | ~r1_tarski(k4_xboole_0(A_1385, k4_xboole_0(A_1386, B_1388)), B_1387))), inference(superposition, [status(thm), theory('equality')], [c_68432, c_5117])).
% 44.45/34.86  tff(c_114836, plain, (![A_1414, A_1415, B_1416]: (r1_tarski(k4_xboole_0(A_1414, A_1415), u1_struct_0('#skF_1')) | ~r1_tarski(k4_xboole_0(A_1414, k4_xboole_0(A_1415, B_1416)), '#skF_2'))), inference(resolution, [status(thm)], [c_101, c_110929])).
% 44.45/34.86  tff(c_115101, plain, (![A_1415]: (r1_tarski(k4_xboole_0('#skF_2', A_1415), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_114836])).
% 44.45/34.86  tff(c_24, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 44.45/34.86  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 44.45/34.86  tff(c_28, plain, (![A_28, B_32, C_34]: (r1_tarski(k1_tops_1(A_28, B_32), k1_tops_1(A_28, C_34)) | ~r1_tarski(B_32, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_88])).
% 44.45/34.86  tff(c_784, plain, (![A_140, B_141]: (r1_tarski(k1_tops_1(A_140, B_141), B_141) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_76])).
% 44.45/34.86  tff(c_1118, plain, (![A_159, A_160]: (r1_tarski(k1_tops_1(A_159, A_160), A_160) | ~l1_pre_topc(A_159) | ~r1_tarski(A_160, u1_struct_0(A_159)))), inference(resolution, [status(thm)], [c_24, c_784])).
% 44.45/34.86  tff(c_74, plain, (![A_50, C_51, B_52]: (r1_xboole_0(A_50, C_51) | ~r1_xboole_0(B_52, C_51) | ~r1_tarski(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_45])).
% 44.45/34.86  tff(c_77, plain, (![A_50, B_16, A_15]: (r1_xboole_0(A_50, B_16) | ~r1_tarski(A_50, k4_xboole_0(A_15, B_16)))), inference(resolution, [status(thm)], [c_16, c_74])).
% 44.45/34.86  tff(c_5459, plain, (![A_337, A_338, B_339]: (r1_xboole_0(k1_tops_1(A_337, k4_xboole_0(A_338, B_339)), B_339) | ~l1_pre_topc(A_337) | ~r1_tarski(k4_xboole_0(A_338, B_339), u1_struct_0(A_337)))), inference(resolution, [status(thm)], [c_1118, c_77])).
% 44.45/34.86  tff(c_57, plain, (![B_48, A_49]: (B_48=A_49 | ~r1_tarski(B_48, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_31])).
% 44.45/34.86  tff(c_68, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, k4_xboole_0(A_6, B_7)))), inference(resolution, [status(thm)], [c_10, c_57])).
% 44.45/34.86  tff(c_264, plain, (![B_92, C_93]: (k4_xboole_0(B_92, C_93)=B_92 | ~r1_xboole_0(B_92, C_93) | ~r1_tarski(B_92, B_92))), inference(resolution, [status(thm)], [c_254, c_68])).
% 44.45/34.86  tff(c_279, plain, (![B_92, C_93]: (k4_xboole_0(B_92, C_93)=B_92 | ~r1_xboole_0(B_92, C_93))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_264])).
% 44.45/34.86  tff(c_159692, plain, (![A_1657, A_1658, B_1659]: (k4_xboole_0(k1_tops_1(A_1657, k4_xboole_0(A_1658, B_1659)), B_1659)=k1_tops_1(A_1657, k4_xboole_0(A_1658, B_1659)) | ~l1_pre_topc(A_1657) | ~r1_tarski(k4_xboole_0(A_1658, B_1659), u1_struct_0(A_1657)))), inference(resolution, [status(thm)], [c_5459, c_279])).
% 44.45/34.86  tff(c_159710, plain, (![A_1415]: (k4_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', A_1415)), A_1415)=k1_tops_1('#skF_1', k4_xboole_0('#skF_2', A_1415)) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_115101, c_159692])).
% 44.45/34.86  tff(c_161573, plain, (![A_1676]: (k4_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', A_1676)), A_1676)=k1_tops_1('#skF_1', k4_xboole_0('#skF_2', A_1676)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_159710])).
% 44.45/34.86  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 44.45/34.86  tff(c_791, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_784])).
% 44.45/34.86  tff(c_798, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_791])).
% 44.45/34.86  tff(c_574, plain, (![A_115, C_116, B_16, A_15]: (r1_xboole_0(A_115, C_116) | ~r1_tarski(C_116, B_16) | ~r1_tarski(A_115, k4_xboole_0(A_15, B_16)))), inference(resolution, [status(thm)], [c_16, c_565])).
% 44.45/34.86  tff(c_1252, plain, (![A_163, A_164]: (r1_xboole_0(A_163, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(A_163, k4_xboole_0(A_164, '#skF_3')))), inference(resolution, [status(thm)], [c_798, c_574])).
% 44.45/34.86  tff(c_1279, plain, (![A_164]: (r1_xboole_0(k4_xboole_0(A_164, '#skF_3'), k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_6, c_1252])).
% 44.45/34.86  tff(c_163264, plain, (r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_161573, c_1279])).
% 44.45/34.86  tff(c_789, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_784])).
% 44.45/34.86  tff(c_795, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_789])).
% 44.45/34.86  tff(c_115, plain, (![A_63]: (r1_tarski(A_63, u1_struct_0('#skF_1')) | ~r1_tarski(A_63, '#skF_2'))), inference(resolution, [status(thm)], [c_55, c_91])).
% 44.45/34.86  tff(c_120, plain, (![A_3, A_63]: (r1_tarski(A_3, u1_struct_0('#skF_1')) | ~r1_tarski(A_3, A_63) | ~r1_tarski(A_63, '#skF_2'))), inference(resolution, [status(thm)], [c_115, c_8])).
% 44.45/34.86  tff(c_804, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_795, c_120])).
% 44.45/34.86  tff(c_815, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_804])).
% 44.45/34.86  tff(c_151, plain, (![A_70, B_71, C_72]: (k7_subset_1(A_70, B_71, C_72)=k4_xboole_0(B_71, C_72) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 44.45/34.86  tff(c_158, plain, (![B_24, A_23, C_72]: (k7_subset_1(B_24, A_23, C_72)=k4_xboole_0(A_23, C_72) | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_24, c_151])).
% 44.45/34.86  tff(c_856, plain, (![C_72]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_72)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_72))), inference(resolution, [status(thm)], [c_815, c_158])).
% 44.45/34.86  tff(c_159, plain, (![C_72]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_72)=k4_xboole_0('#skF_2', C_72))), inference(resolution, [status(thm)], [c_34, c_151])).
% 44.45/34.86  tff(c_30, plain, (~r1_tarski(k1_tops_1('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 44.45/34.86  tff(c_161, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_30])).
% 44.45/34.86  tff(c_18559, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_856, c_161])).
% 44.45/34.86  tff(c_18798, plain, (~r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_18559])).
% 44.45/34.86  tff(c_172474, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_163264, c_18798])).
% 44.45/34.86  tff(c_172477, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k4_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_172474])).
% 44.45/34.86  tff(c_172480, plain, (~m1_subset_1(k4_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_10, c_172477])).
% 44.45/34.86  tff(c_172483, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_172480])).
% 44.45/34.86  tff(c_172487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115101, c_172483])).
% 44.45/34.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 44.45/34.86  
% 44.45/34.86  Inference rules
% 44.45/34.86  ----------------------
% 44.45/34.86  #Ref     : 0
% 44.45/34.86  #Sup     : 43639
% 44.45/34.86  #Fact    : 0
% 44.45/34.86  #Define  : 0
% 44.45/34.86  #Split   : 17
% 44.45/34.86  #Chain   : 0
% 44.45/34.86  #Close   : 0
% 44.45/34.86  
% 44.45/34.86  Ordering : KBO
% 44.45/34.86  
% 44.45/34.86  Simplification rules
% 44.45/34.86  ----------------------
% 44.45/34.86  #Subsume      : 11723
% 44.45/34.86  #Demod        : 20535
% 44.45/34.86  #Tautology    : 14717
% 44.45/34.86  #SimpNegUnit  : 44
% 44.45/34.86  #BackRed      : 6
% 44.45/34.86  
% 44.45/34.86  #Partial instantiations: 0
% 44.45/34.86  #Strategies tried      : 1
% 44.45/34.86  
% 44.45/34.86  Timing (in seconds)
% 44.45/34.86  ----------------------
% 44.45/34.86  Preprocessing        : 0.30
% 44.45/34.86  Parsing              : 0.16
% 44.45/34.86  CNF conversion       : 0.02
% 44.45/34.86  Main loop            : 33.73
% 44.45/34.86  Inferencing          : 2.81
% 44.45/34.86  Reduction            : 16.66
% 44.45/34.86  Demodulation         : 14.68
% 44.45/34.86  BG Simplification    : 0.35
% 44.45/34.86  Subsumption          : 12.63
% 44.45/34.86  Abstraction          : 0.58
% 44.45/34.86  MUC search           : 0.00
% 44.45/34.86  Cooper               : 0.00
% 44.45/34.86  Total                : 34.08
% 44.45/34.86  Index Insertion      : 0.00
% 44.45/34.86  Index Deletion       : 0.00
% 44.45/34.86  Index Matching       : 0.00
% 44.45/34.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
