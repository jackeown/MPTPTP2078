%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:36 EST 2020

% Result     : Theorem 4.94s
% Output     : CNFRefutation 5.27s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 778 expanded)
%              Number of leaves         :   30 ( 279 expanded)
%              Depth                    :   19
%              Number of atoms          :  180 (1722 expanded)
%              Number of equality atoms :   87 ( 644 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ~ ( B != k2_struct_0(A)
                  & k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) = k1_xboole_0 )
              & ~ ( k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) != k1_xboole_0
                  & B = k2_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_pre_topc)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k4_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k4_subset_1(u1_struct_0(A),B,k3_subset_1(u1_struct_0(A),B)) = k2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_pre_topc)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k3_subset_1(A,k7_subset_1(A,B,C)) = k4_subset_1(A,k3_subset_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(A_27,k1_zfmisc_1(B_28))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_78,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,B_43) = k3_subset_1(A_42,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [B_44,A_45] :
      ( k4_xboole_0(B_44,A_45) = k3_subset_1(B_44,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(resolution,[status(thm)],[c_28,c_78])).

tff(c_100,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k3_subset_1(B_2,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_91])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_190,plain,(
    ! [A_55,B_56,C_57] :
      ( k7_subset_1(A_55,B_56,C_57) = k4_xboole_0(B_56,C_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_199,plain,(
    ! [C_57] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_57) = k4_xboole_0('#skF_2',C_57) ),
    inference(resolution,[status(thm)],[c_32,c_190])).

tff(c_36,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k1_xboole_0
    | k2_struct_0('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_73,plain,(
    k2_struct_0('#skF_1') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_42,plain,
    ( k2_struct_0('#skF_1') != '#skF_2'
    | k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_138,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_73,c_42])).

tff(c_200,plain,(
    k4_xboole_0('#skF_2','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_138])).

tff(c_201,plain,(
    k3_subset_1('#skF_2','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_200])).

tff(c_211,plain,(
    ! [A_59,B_60,C_61] :
      ( k4_subset_1(A_59,B_60,B_60) = B_60
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_241,plain,(
    ! [B_67] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_67,B_67) = B_67
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_211])).

tff(c_252,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_241])).

tff(c_306,plain,(
    ! [A_77,B_78,C_79] :
      ( k4_subset_1(A_77,B_78,C_79) = k2_xboole_0(B_78,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_77))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_326,plain,(
    ! [B_81] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_81,'#skF_2') = k2_xboole_0(B_81,'#skF_2')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_306])).

tff(c_337,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_2') = k2_xboole_0('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_326])).

tff(c_341,plain,(
    k2_xboole_0('#skF_2','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_337])).

tff(c_8,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_345,plain,(
    k4_xboole_0('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_8])).

tff(c_352,plain,(
    k3_subset_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_100])).

tff(c_359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_352])).

tff(c_361,plain,(
    k2_struct_0('#skF_1') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_444,plain,(
    ! [A_91,B_92] :
      ( m1_subset_1(k3_subset_1(A_91,B_92),k1_zfmisc_1(A_91))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | ~ m1_subset_1(A_27,k1_zfmisc_1(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_461,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(k3_subset_1(A_91,B_92),A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(resolution,[status(thm)],[c_444,c_26])).

tff(c_581,plain,(
    ! [A_115,B_116,C_117] :
      ( k4_subset_1(A_115,B_116,C_117) = k2_xboole_0(B_116,C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(A_115))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1256,plain,(
    ! [B_154,B_155,A_156] :
      ( k4_subset_1(B_154,B_155,A_156) = k2_xboole_0(B_155,A_156)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(B_154))
      | ~ r1_tarski(A_156,B_154) ) ),
    inference(resolution,[status(thm)],[c_28,c_581])).

tff(c_1306,plain,(
    ! [A_159] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_159) = k2_xboole_0('#skF_2',A_159)
      | ~ r1_tarski(A_159,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_32,c_1256])).

tff(c_1437,plain,(
    ! [B_162] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k3_subset_1(u1_struct_0('#skF_1'),B_162)) = k2_xboole_0('#skF_2',k3_subset_1(u1_struct_0('#skF_1'),B_162))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_461,c_1306])).

tff(c_30,plain,(
    ! [A_29,B_31] :
      ( k4_subset_1(u1_struct_0(A_29),B_31,k3_subset_1(u1_struct_0(A_29),B_31)) = k2_struct_0(A_29)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1444,plain,
    ( k2_xboole_0('#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1437,c_30])).

tff(c_1465,plain,(
    k2_xboole_0('#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_32,c_1444])).

tff(c_53,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_61,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_53])).

tff(c_488,plain,(
    ! [A_98,B_99,C_100] :
      ( k4_subset_1(A_98,B_99,B_99) = B_99
      | ~ m1_subset_1(C_100,k1_zfmisc_1(A_98))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_560,plain,(
    ! [B_109,B_110,A_111] :
      ( k4_subset_1(B_109,B_110,B_110) = B_110
      | ~ m1_subset_1(B_110,k1_zfmisc_1(B_109))
      | ~ r1_tarski(A_111,B_109) ) ),
    inference(resolution,[status(thm)],[c_28,c_488])).

tff(c_571,plain,(
    ! [B_112,A_113,A_114] :
      ( k4_subset_1(B_112,A_113,A_113) = A_113
      | ~ r1_tarski(A_114,B_112)
      | ~ r1_tarski(A_113,B_112) ) ),
    inference(resolution,[status(thm)],[c_28,c_560])).

tff(c_591,plain,(
    ! [B_118,A_119] :
      ( k4_subset_1(B_118,A_119,A_119) = A_119
      | ~ r1_tarski(A_119,B_118) ) ),
    inference(resolution,[status(thm)],[c_6,c_571])).

tff(c_601,plain,(
    ! [B_2] : k4_subset_1(B_2,B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_591])).

tff(c_1482,plain,(
    ! [B_163,A_164,A_165] :
      ( k4_subset_1(B_163,A_164,A_165) = k2_xboole_0(A_164,A_165)
      | ~ r1_tarski(A_165,B_163)
      | ~ r1_tarski(A_164,B_163) ) ),
    inference(resolution,[status(thm)],[c_28,c_1256])).

tff(c_1495,plain,(
    ! [B_166,A_167] :
      ( k4_subset_1(B_166,A_167,B_166) = k2_xboole_0(A_167,B_166)
      | ~ r1_tarski(A_167,B_166) ) ),
    inference(resolution,[status(thm)],[c_6,c_1482])).

tff(c_1503,plain,(
    ! [B_2] : k4_subset_1(B_2,B_2,B_2) = k2_xboole_0(B_2,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_1495])).

tff(c_1531,plain,(
    ! [B_171] : k2_xboole_0(B_171,B_171) = B_171 ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_1503])).

tff(c_1537,plain,(
    ! [B_171] : k4_xboole_0(B_171,B_171) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1531,c_8])).

tff(c_366,plain,(
    ! [A_82,B_83] :
      ( k4_xboole_0(A_82,B_83) = k3_subset_1(A_82,B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_390,plain,(
    ! [B_86,A_87] :
      ( k4_xboole_0(B_86,A_87) = k3_subset_1(B_86,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(resolution,[status(thm)],[c_28,c_366])).

tff(c_399,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k3_subset_1(B_2,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_390])).

tff(c_1555,plain,(
    ! [B_173] : k3_subset_1(B_173,B_173) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1537,c_399])).

tff(c_375,plain,(
    ! [A_84,B_85] :
      ( k3_subset_1(A_84,k3_subset_1(A_84,B_85)) = B_85
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_380,plain,(
    ! [B_28,A_27] :
      ( k3_subset_1(B_28,k3_subset_1(B_28,A_27)) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_28,c_375])).

tff(c_1591,plain,(
    ! [B_173] :
      ( k3_subset_1(B_173,k1_xboole_0) = B_173
      | ~ r1_tarski(B_173,B_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1555,c_380])).

tff(c_1603,plain,(
    ! [B_173] : k3_subset_1(B_173,k1_xboole_0) = B_173 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1591])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k3_subset_1(A_10,B_11),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_676,plain,(
    ! [A_122,C_123,B_124] :
      ( k4_subset_1(A_122,C_123,B_124) = k4_subset_1(A_122,B_124,C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(A_122))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(A_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2518,plain,(
    ! [A_209,B_210,B_211] :
      ( k4_subset_1(A_209,k3_subset_1(A_209,B_210),B_211) = k4_subset_1(A_209,B_211,k3_subset_1(A_209,B_210))
      | ~ m1_subset_1(B_211,k1_zfmisc_1(A_209))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(A_209)) ) ),
    inference(resolution,[status(thm)],[c_14,c_676])).

tff(c_2578,plain,(
    ! [B_215] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),B_215),'#skF_2') = k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k3_subset_1(u1_struct_0('#skF_1'),B_215))
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_2518])).

tff(c_478,plain,(
    ! [A_95,B_96,C_97] :
      ( k7_subset_1(A_95,B_96,C_97) = k4_xboole_0(B_96,C_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_487,plain,(
    ! [C_97] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_97) = k4_xboole_0('#skF_2',C_97) ),
    inference(resolution,[status(thm)],[c_32,c_478])).

tff(c_892,plain,(
    ! [A_132,B_133,C_134] :
      ( k4_subset_1(A_132,k3_subset_1(A_132,B_133),C_134) = k3_subset_1(A_132,k7_subset_1(A_132,B_133,C_134))
      | ~ m1_subset_1(C_134,k1_zfmisc_1(A_132))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2147,plain,(
    ! [B_192,B_193,A_194] :
      ( k4_subset_1(B_192,k3_subset_1(B_192,B_193),A_194) = k3_subset_1(B_192,k7_subset_1(B_192,B_193,A_194))
      | ~ m1_subset_1(B_193,k1_zfmisc_1(B_192))
      | ~ r1_tarski(A_194,B_192) ) ),
    inference(resolution,[status(thm)],[c_28,c_892])).

tff(c_2157,plain,(
    ! [A_194] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),A_194) = k3_subset_1(u1_struct_0('#skF_1'),k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_194))
      | ~ r1_tarski(A_194,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_32,c_2147])).

tff(c_2165,plain,(
    ! [A_194] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),A_194) = k3_subset_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2',A_194))
      | ~ r1_tarski(A_194,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_2157])).

tff(c_2585,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_2'))
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2578,c_2165])).

tff(c_2626,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_61,c_1603,c_1537,c_2585])).

tff(c_1318,plain,(
    ! [B_92] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k3_subset_1(u1_struct_0('#skF_1'),B_92)) = k2_xboole_0('#skF_2',k3_subset_1(u1_struct_0('#skF_1'),B_92))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_461,c_1306])).

tff(c_2694,plain,
    ( k2_xboole_0('#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = u1_struct_0('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2626,c_1318])).

tff(c_2707,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1465,c_2694])).

tff(c_2745,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2707,c_61])).

tff(c_360,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2743,plain,(
    k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2707,c_360])).

tff(c_507,plain,(
    ! [B_102,A_103,C_104] :
      ( k7_subset_1(B_102,A_103,C_104) = k4_xboole_0(A_103,C_104)
      | ~ r1_tarski(A_103,B_102) ) ),
    inference(resolution,[status(thm)],[c_28,c_478])).

tff(c_517,plain,(
    ! [B_2,C_104] : k7_subset_1(B_2,B_2,C_104) = k4_xboole_0(B_2,C_104) ),
    inference(resolution,[status(thm)],[c_6,c_507])).

tff(c_2915,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2743,c_517])).

tff(c_374,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_366])).

tff(c_2742,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2707,c_2707,c_374])).

tff(c_3063,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2915,c_2742])).

tff(c_3096,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3063,c_380])).

tff(c_3116,plain,(
    k2_struct_0('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2745,c_1603,c_3096])).

tff(c_3118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_361,c_3116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:51:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.94/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.94/1.96  
% 4.94/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.94/1.96  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.94/1.96  
% 4.94/1.96  %Foreground sorts:
% 4.94/1.96  
% 4.94/1.96  
% 4.94/1.96  %Background operators:
% 4.94/1.96  
% 4.94/1.96  
% 4.94/1.96  %Foreground operators:
% 4.94/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.94/1.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.94/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.94/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.94/1.96  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.94/1.96  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.94/1.96  tff('#skF_2', type, '#skF_2': $i).
% 4.94/1.96  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.94/1.96  tff('#skF_1', type, '#skF_1': $i).
% 4.94/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.94/1.96  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.94/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.94/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.94/1.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.94/1.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.94/1.96  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.94/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.94/1.96  
% 5.27/1.98  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.27/1.98  tff(f_78, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.27/1.98  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 5.27/1.98  tff(f_103, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~(~(B = k2_struct_0(A)) & (k7_subset_1(u1_struct_0(A), k2_struct_0(A), B) = k1_xboole_0)) & ~(~(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B) = k1_xboole_0) & (B = k2_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_pre_topc)).
% 5.27/1.98  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.27/1.98  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k4_subset_1)).
% 5.27/1.98  tff(f_63, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.27/1.98  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.27/1.98  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.27/1.98  tff(f_85, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k4_subset_1(u1_struct_0(A), B, k3_subset_1(u1_struct_0(A), B)) = k2_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_pre_topc)).
% 5.27/1.98  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.27/1.98  tff(f_39, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 5.27/1.98  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k3_subset_1(A, k7_subset_1(A, B, C)) = k4_subset_1(A, k3_subset_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_subset_1)).
% 5.27/1.98  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.27/1.98  tff(c_28, plain, (![A_27, B_28]: (m1_subset_1(A_27, k1_zfmisc_1(B_28)) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.27/1.98  tff(c_78, plain, (![A_42, B_43]: (k4_xboole_0(A_42, B_43)=k3_subset_1(A_42, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.27/1.98  tff(c_91, plain, (![B_44, A_45]: (k4_xboole_0(B_44, A_45)=k3_subset_1(B_44, A_45) | ~r1_tarski(A_45, B_44))), inference(resolution, [status(thm)], [c_28, c_78])).
% 5.27/1.98  tff(c_100, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k3_subset_1(B_2, B_2))), inference(resolution, [status(thm)], [c_6, c_91])).
% 5.27/1.98  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.27/1.98  tff(c_190, plain, (![A_55, B_56, C_57]: (k7_subset_1(A_55, B_56, C_57)=k4_xboole_0(B_56, C_57) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.27/1.98  tff(c_199, plain, (![C_57]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_57)=k4_xboole_0('#skF_2', C_57))), inference(resolution, [status(thm)], [c_32, c_190])).
% 5.27/1.98  tff(c_36, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')=k1_xboole_0 | k2_struct_0('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.27/1.98  tff(c_73, plain, (k2_struct_0('#skF_1')='#skF_2'), inference(splitLeft, [status(thm)], [c_36])).
% 5.27/1.98  tff(c_42, plain, (k2_struct_0('#skF_1')!='#skF_2' | k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.27/1.98  tff(c_138, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_73, c_73, c_42])).
% 5.27/1.98  tff(c_200, plain, (k4_xboole_0('#skF_2', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_199, c_138])).
% 5.27/1.98  tff(c_201, plain, (k3_subset_1('#skF_2', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_100, c_200])).
% 5.27/1.98  tff(c_211, plain, (![A_59, B_60, C_61]: (k4_subset_1(A_59, B_60, B_60)=B_60 | ~m1_subset_1(C_61, k1_zfmisc_1(A_59)) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.27/1.98  tff(c_241, plain, (![B_67]: (k4_subset_1(u1_struct_0('#skF_1'), B_67, B_67)=B_67 | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_32, c_211])).
% 5.27/1.98  tff(c_252, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_32, c_241])).
% 5.27/1.98  tff(c_306, plain, (![A_77, B_78, C_79]: (k4_subset_1(A_77, B_78, C_79)=k2_xboole_0(B_78, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(A_77)) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.27/1.98  tff(c_326, plain, (![B_81]: (k4_subset_1(u1_struct_0('#skF_1'), B_81, '#skF_2')=k2_xboole_0(B_81, '#skF_2') | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_32, c_306])).
% 5.27/1.98  tff(c_337, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_2')=k2_xboole_0('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_326])).
% 5.27/1.98  tff(c_341, plain, (k2_xboole_0('#skF_2', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_252, c_337])).
% 5.27/1.98  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.27/1.98  tff(c_345, plain, (k4_xboole_0('#skF_2', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_341, c_8])).
% 5.27/1.98  tff(c_352, plain, (k3_subset_1('#skF_2', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_345, c_100])).
% 5.27/1.98  tff(c_359, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_352])).
% 5.27/1.98  tff(c_361, plain, (k2_struct_0('#skF_1')!='#skF_2'), inference(splitRight, [status(thm)], [c_36])).
% 5.27/1.98  tff(c_34, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.27/1.98  tff(c_444, plain, (![A_91, B_92]: (m1_subset_1(k3_subset_1(A_91, B_92), k1_zfmisc_1(A_91)) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.27/1.98  tff(c_26, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | ~m1_subset_1(A_27, k1_zfmisc_1(B_28)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.27/1.98  tff(c_461, plain, (![A_91, B_92]: (r1_tarski(k3_subset_1(A_91, B_92), A_91) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(resolution, [status(thm)], [c_444, c_26])).
% 5.27/1.98  tff(c_581, plain, (![A_115, B_116, C_117]: (k4_subset_1(A_115, B_116, C_117)=k2_xboole_0(B_116, C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(A_115)) | ~m1_subset_1(B_116, k1_zfmisc_1(A_115)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.27/1.98  tff(c_1256, plain, (![B_154, B_155, A_156]: (k4_subset_1(B_154, B_155, A_156)=k2_xboole_0(B_155, A_156) | ~m1_subset_1(B_155, k1_zfmisc_1(B_154)) | ~r1_tarski(A_156, B_154))), inference(resolution, [status(thm)], [c_28, c_581])).
% 5.27/1.98  tff(c_1306, plain, (![A_159]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_159)=k2_xboole_0('#skF_2', A_159) | ~r1_tarski(A_159, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_32, c_1256])).
% 5.27/1.98  tff(c_1437, plain, (![B_162]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k3_subset_1(u1_struct_0('#skF_1'), B_162))=k2_xboole_0('#skF_2', k3_subset_1(u1_struct_0('#skF_1'), B_162)) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_461, c_1306])).
% 5.27/1.98  tff(c_30, plain, (![A_29, B_31]: (k4_subset_1(u1_struct_0(A_29), B_31, k3_subset_1(u1_struct_0(A_29), B_31))=k2_struct_0(A_29) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.27/1.98  tff(c_1444, plain, (k2_xboole_0('#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1437, c_30])).
% 5.27/1.98  tff(c_1465, plain, (k2_xboole_0('#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_32, c_1444])).
% 5.27/1.98  tff(c_53, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.27/1.98  tff(c_61, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_53])).
% 5.27/1.98  tff(c_488, plain, (![A_98, B_99, C_100]: (k4_subset_1(A_98, B_99, B_99)=B_99 | ~m1_subset_1(C_100, k1_zfmisc_1(A_98)) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.27/1.98  tff(c_560, plain, (![B_109, B_110, A_111]: (k4_subset_1(B_109, B_110, B_110)=B_110 | ~m1_subset_1(B_110, k1_zfmisc_1(B_109)) | ~r1_tarski(A_111, B_109))), inference(resolution, [status(thm)], [c_28, c_488])).
% 5.27/1.98  tff(c_571, plain, (![B_112, A_113, A_114]: (k4_subset_1(B_112, A_113, A_113)=A_113 | ~r1_tarski(A_114, B_112) | ~r1_tarski(A_113, B_112))), inference(resolution, [status(thm)], [c_28, c_560])).
% 5.27/1.98  tff(c_591, plain, (![B_118, A_119]: (k4_subset_1(B_118, A_119, A_119)=A_119 | ~r1_tarski(A_119, B_118))), inference(resolution, [status(thm)], [c_6, c_571])).
% 5.27/1.98  tff(c_601, plain, (![B_2]: (k4_subset_1(B_2, B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_591])).
% 5.27/1.98  tff(c_1482, plain, (![B_163, A_164, A_165]: (k4_subset_1(B_163, A_164, A_165)=k2_xboole_0(A_164, A_165) | ~r1_tarski(A_165, B_163) | ~r1_tarski(A_164, B_163))), inference(resolution, [status(thm)], [c_28, c_1256])).
% 5.27/1.98  tff(c_1495, plain, (![B_166, A_167]: (k4_subset_1(B_166, A_167, B_166)=k2_xboole_0(A_167, B_166) | ~r1_tarski(A_167, B_166))), inference(resolution, [status(thm)], [c_6, c_1482])).
% 5.27/1.98  tff(c_1503, plain, (![B_2]: (k4_subset_1(B_2, B_2, B_2)=k2_xboole_0(B_2, B_2))), inference(resolution, [status(thm)], [c_6, c_1495])).
% 5.27/1.98  tff(c_1531, plain, (![B_171]: (k2_xboole_0(B_171, B_171)=B_171)), inference(demodulation, [status(thm), theory('equality')], [c_601, c_1503])).
% 5.27/1.98  tff(c_1537, plain, (![B_171]: (k4_xboole_0(B_171, B_171)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1531, c_8])).
% 5.27/1.98  tff(c_366, plain, (![A_82, B_83]: (k4_xboole_0(A_82, B_83)=k3_subset_1(A_82, B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.27/1.98  tff(c_390, plain, (![B_86, A_87]: (k4_xboole_0(B_86, A_87)=k3_subset_1(B_86, A_87) | ~r1_tarski(A_87, B_86))), inference(resolution, [status(thm)], [c_28, c_366])).
% 5.27/1.98  tff(c_399, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k3_subset_1(B_2, B_2))), inference(resolution, [status(thm)], [c_6, c_390])).
% 5.27/1.98  tff(c_1555, plain, (![B_173]: (k3_subset_1(B_173, B_173)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1537, c_399])).
% 5.27/1.98  tff(c_375, plain, (![A_84, B_85]: (k3_subset_1(A_84, k3_subset_1(A_84, B_85))=B_85 | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.27/1.98  tff(c_380, plain, (![B_28, A_27]: (k3_subset_1(B_28, k3_subset_1(B_28, A_27))=A_27 | ~r1_tarski(A_27, B_28))), inference(resolution, [status(thm)], [c_28, c_375])).
% 5.27/1.98  tff(c_1591, plain, (![B_173]: (k3_subset_1(B_173, k1_xboole_0)=B_173 | ~r1_tarski(B_173, B_173))), inference(superposition, [status(thm), theory('equality')], [c_1555, c_380])).
% 5.27/1.98  tff(c_1603, plain, (![B_173]: (k3_subset_1(B_173, k1_xboole_0)=B_173)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1591])).
% 5.27/1.98  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(k3_subset_1(A_10, B_11), k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.27/1.98  tff(c_676, plain, (![A_122, C_123, B_124]: (k4_subset_1(A_122, C_123, B_124)=k4_subset_1(A_122, B_124, C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(A_122)) | ~m1_subset_1(B_124, k1_zfmisc_1(A_122)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.27/1.98  tff(c_2518, plain, (![A_209, B_210, B_211]: (k4_subset_1(A_209, k3_subset_1(A_209, B_210), B_211)=k4_subset_1(A_209, B_211, k3_subset_1(A_209, B_210)) | ~m1_subset_1(B_211, k1_zfmisc_1(A_209)) | ~m1_subset_1(B_210, k1_zfmisc_1(A_209)))), inference(resolution, [status(thm)], [c_14, c_676])).
% 5.27/1.98  tff(c_2578, plain, (![B_215]: (k4_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), B_215), '#skF_2')=k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k3_subset_1(u1_struct_0('#skF_1'), B_215)) | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_32, c_2518])).
% 5.27/1.98  tff(c_478, plain, (![A_95, B_96, C_97]: (k7_subset_1(A_95, B_96, C_97)=k4_xboole_0(B_96, C_97) | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.27/1.98  tff(c_487, plain, (![C_97]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_97)=k4_xboole_0('#skF_2', C_97))), inference(resolution, [status(thm)], [c_32, c_478])).
% 5.27/1.98  tff(c_892, plain, (![A_132, B_133, C_134]: (k4_subset_1(A_132, k3_subset_1(A_132, B_133), C_134)=k3_subset_1(A_132, k7_subset_1(A_132, B_133, C_134)) | ~m1_subset_1(C_134, k1_zfmisc_1(A_132)) | ~m1_subset_1(B_133, k1_zfmisc_1(A_132)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.27/1.98  tff(c_2147, plain, (![B_192, B_193, A_194]: (k4_subset_1(B_192, k3_subset_1(B_192, B_193), A_194)=k3_subset_1(B_192, k7_subset_1(B_192, B_193, A_194)) | ~m1_subset_1(B_193, k1_zfmisc_1(B_192)) | ~r1_tarski(A_194, B_192))), inference(resolution, [status(thm)], [c_28, c_892])).
% 5.27/1.98  tff(c_2157, plain, (![A_194]: (k4_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), A_194)=k3_subset_1(u1_struct_0('#skF_1'), k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_194)) | ~r1_tarski(A_194, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_32, c_2147])).
% 5.27/1.98  tff(c_2165, plain, (![A_194]: (k4_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), A_194)=k3_subset_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', A_194)) | ~r1_tarski(A_194, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_487, c_2157])).
% 5.27/1.98  tff(c_2585, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_2')) | ~r1_tarski('#skF_2', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2578, c_2165])).
% 5.27/1.98  tff(c_2626, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_61, c_1603, c_1537, c_2585])).
% 5.27/1.98  tff(c_1318, plain, (![B_92]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k3_subset_1(u1_struct_0('#skF_1'), B_92))=k2_xboole_0('#skF_2', k3_subset_1(u1_struct_0('#skF_1'), B_92)) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_461, c_1306])).
% 5.27/1.98  tff(c_2694, plain, (k2_xboole_0('#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=u1_struct_0('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2626, c_1318])).
% 5.27/1.98  tff(c_2707, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1465, c_2694])).
% 5.27/1.98  tff(c_2745, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2707, c_61])).
% 5.27/1.98  tff(c_360, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 5.27/1.98  tff(c_2743, plain, (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2707, c_360])).
% 5.27/1.98  tff(c_507, plain, (![B_102, A_103, C_104]: (k7_subset_1(B_102, A_103, C_104)=k4_xboole_0(A_103, C_104) | ~r1_tarski(A_103, B_102))), inference(resolution, [status(thm)], [c_28, c_478])).
% 5.27/1.98  tff(c_517, plain, (![B_2, C_104]: (k7_subset_1(B_2, B_2, C_104)=k4_xboole_0(B_2, C_104))), inference(resolution, [status(thm)], [c_6, c_507])).
% 5.27/1.98  tff(c_2915, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2743, c_517])).
% 5.27/1.98  tff(c_374, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_32, c_366])).
% 5.27/1.98  tff(c_2742, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2707, c_2707, c_374])).
% 5.27/1.98  tff(c_3063, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2915, c_2742])).
% 5.27/1.98  tff(c_3096, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_xboole_0)='#skF_2' | ~r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3063, c_380])).
% 5.27/1.98  tff(c_3116, plain, (k2_struct_0('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2745, c_1603, c_3096])).
% 5.27/1.98  tff(c_3118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_361, c_3116])).
% 5.27/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.27/1.98  
% 5.27/1.98  Inference rules
% 5.27/1.98  ----------------------
% 5.27/1.98  #Ref     : 0
% 5.27/1.98  #Sup     : 746
% 5.27/1.98  #Fact    : 0
% 5.27/1.98  #Define  : 0
% 5.27/1.98  #Split   : 4
% 5.27/1.98  #Chain   : 0
% 5.27/1.98  #Close   : 0
% 5.27/1.98  
% 5.27/1.98  Ordering : KBO
% 5.27/1.98  
% 5.27/1.98  Simplification rules
% 5.27/1.98  ----------------------
% 5.27/1.98  #Subsume      : 48
% 5.27/1.98  #Demod        : 590
% 5.27/1.98  #Tautology    : 440
% 5.27/1.98  #SimpNegUnit  : 4
% 5.27/1.98  #BackRed      : 42
% 5.27/1.98  
% 5.27/1.98  #Partial instantiations: 0
% 5.27/1.98  #Strategies tried      : 1
% 5.27/1.98  
% 5.27/1.98  Timing (in seconds)
% 5.27/1.98  ----------------------
% 5.27/1.99  Preprocessing        : 0.35
% 5.27/1.99  Parsing              : 0.19
% 5.27/1.99  CNF conversion       : 0.02
% 5.27/1.99  Main loop            : 0.84
% 5.27/1.99  Inferencing          : 0.28
% 5.27/1.99  Reduction            : 0.28
% 5.27/1.99  Demodulation         : 0.21
% 5.27/1.99  BG Simplification    : 0.04
% 5.27/1.99  Subsumption          : 0.17
% 5.27/1.99  Abstraction          : 0.05
% 5.27/1.99  MUC search           : 0.00
% 5.27/1.99  Cooper               : 0.00
% 5.27/1.99  Total                : 1.23
% 5.27/1.99  Index Insertion      : 0.00
% 5.27/1.99  Index Deletion       : 0.00
% 5.27/1.99  Index Matching       : 0.00
% 5.27/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
