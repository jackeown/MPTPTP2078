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
% DateTime   : Thu Dec  3 10:20:08 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 453 expanded)
%              Number of leaves         :   34 ( 184 expanded)
%              Depth                    :   20
%              Number of atoms          :  219 (1612 expanded)
%              Number of equality atoms :   37 ( 230 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_114,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( C = k4_orders_2(A,B)
            <=> ! [D] :
                  ( r2_hidden(D,C)
                <=> m2_orders_2(D,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_37,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_34,plain,(
    k3_tarski(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [A_56,B_57] :
      ( k3_tarski(A_56) != k1_xboole_0
      | ~ r2_hidden(B_57,A_56)
      | k1_xboole_0 = B_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_86,plain,(
    ! [A_1,B_2] :
      ( k3_tarski(A_1) != k1_xboole_0
      | '#skF_1'(A_1,B_2) = k1_xboole_0
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_88,plain,(
    ! [C_58,B_59,A_60] :
      ( r2_hidden(C_58,B_59)
      | ~ r2_hidden(C_58,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_139,plain,(
    ! [A_69,B_70,B_71] :
      ( r2_hidden('#skF_1'(A_69,B_70),B_71)
      | ~ r1_tarski(A_69,B_71)
      | r1_tarski(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_88])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_389,plain,(
    ! [A_104,B_105,B_106,B_107] :
      ( r2_hidden('#skF_1'(A_104,B_105),B_106)
      | ~ r1_tarski(B_107,B_106)
      | ~ r1_tarski(A_104,B_107)
      | r1_tarski(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_139,c_2])).

tff(c_404,plain,(
    ! [A_111,B_112,A_113] :
      ( r2_hidden('#skF_1'(A_111,B_112),A_113)
      | ~ r1_tarski(A_111,k1_xboole_0)
      | r1_tarski(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_8,c_389])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_428,plain,(
    ! [A_114,A_115] :
      ( ~ r1_tarski(A_114,k1_xboole_0)
      | r1_tarski(A_114,A_115) ) ),
    inference(resolution,[status(thm)],[c_404,c_4])).

tff(c_459,plain,(
    ! [A_118,A_119] :
      ( r1_tarski(A_118,A_119)
      | k3_tarski(A_118) != k1_xboole_0
      | '#skF_1'(A_118,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_86,c_428])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_42,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_38,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_36,plain,(
    m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_120,plain,(
    ! [A_67,B_68] :
      ( m2_orders_2('#skF_4'(A_67,B_68),A_67,B_68)
      | ~ m1_orders_1(B_68,k1_orders_1(u1_struct_0(A_67)))
      | ~ l1_orders_2(A_67)
      | ~ v5_orders_2(A_67)
      | ~ v4_orders_2(A_67)
      | ~ v3_orders_2(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_122,plain,
    ( m2_orders_2('#skF_4'('#skF_6','#skF_7'),'#skF_6','#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_120])).

tff(c_125,plain,
    ( m2_orders_2('#skF_4'('#skF_6','#skF_7'),'#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_122])).

tff(c_126,plain,(
    m2_orders_2('#skF_4'('#skF_6','#skF_7'),'#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_125])).

tff(c_244,plain,(
    ! [D_86,A_87,B_88] :
      ( r2_hidden(D_86,k4_orders_2(A_87,B_88))
      | ~ m2_orders_2(D_86,A_87,B_88)
      | ~ m1_orders_1(B_88,k1_orders_1(u1_struct_0(A_87)))
      | ~ l1_orders_2(A_87)
      | ~ v5_orders_2(A_87)
      | ~ v4_orders_2(A_87)
      | ~ v3_orders_2(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_246,plain,(
    ! [D_86] :
      ( r2_hidden(D_86,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_86,'#skF_6','#skF_7')
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_244])).

tff(c_249,plain,(
    ! [D_86] :
      ( r2_hidden(D_86,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_86,'#skF_6','#skF_7')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_246])).

tff(c_251,plain,(
    ! [D_89] :
      ( r2_hidden(D_89,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_89,'#skF_6','#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_249])).

tff(c_28,plain,(
    ! [A_41,B_44] :
      ( k3_tarski(A_41) != k1_xboole_0
      | ~ r2_hidden(B_44,A_41)
      | k1_xboole_0 = B_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_258,plain,(
    ! [D_89] :
      ( k3_tarski(k4_orders_2('#skF_6','#skF_7')) != k1_xboole_0
      | k1_xboole_0 = D_89
      | ~ m2_orders_2(D_89,'#skF_6','#skF_7') ) ),
    inference(resolution,[status(thm)],[c_251,c_28])).

tff(c_272,plain,(
    ! [D_90] :
      ( k1_xboole_0 = D_90
      | ~ m2_orders_2(D_90,'#skF_6','#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_258])).

tff(c_276,plain,(
    '#skF_4'('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_126,c_272])).

tff(c_277,plain,(
    m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_126])).

tff(c_287,plain,(
    ! [D_91,B_92] :
      ( r2_hidden(D_91,B_92)
      | ~ r1_tarski(k4_orders_2('#skF_6','#skF_7'),B_92)
      | ~ m2_orders_2(D_91,'#skF_6','#skF_7') ) ),
    inference(resolution,[status(thm)],[c_251,c_2])).

tff(c_290,plain,(
    ! [D_91,B_2] :
      ( r2_hidden(D_91,B_2)
      | ~ m2_orders_2(D_91,'#skF_6','#skF_7')
      | k3_tarski(k4_orders_2('#skF_6','#skF_7')) != k1_xboole_0
      | '#skF_1'(k4_orders_2('#skF_6','#skF_7'),B_2) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_86,c_287])).

tff(c_327,plain,(
    ! [D_100,B_101] :
      ( r2_hidden(D_100,B_101)
      | ~ m2_orders_2(D_100,'#skF_6','#skF_7')
      | '#skF_1'(k4_orders_2('#skF_6','#skF_7'),B_101) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_290])).

tff(c_331,plain,(
    ! [B_102] :
      ( r2_hidden(k1_xboole_0,B_102)
      | '#skF_1'(k4_orders_2('#skF_6','#skF_7'),B_102) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_277,c_327])).

tff(c_350,plain,(
    ! [B_102] :
      ( r2_hidden(k1_xboole_0,k4_orders_2('#skF_6','#skF_7'))
      | r1_tarski(k4_orders_2('#skF_6','#skF_7'),B_102)
      | r2_hidden(k1_xboole_0,B_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_6])).

tff(c_358,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_370,plain,(
    ! [B_2] :
      ( r2_hidden(k1_xboole_0,B_2)
      | ~ r1_tarski(k4_orders_2('#skF_6','#skF_7'),B_2) ) ),
    inference(resolution,[status(thm)],[c_358,c_2])).

tff(c_468,plain,(
    ! [A_119] :
      ( r2_hidden(k1_xboole_0,A_119)
      | k3_tarski(k4_orders_2('#skF_6','#skF_7')) != k1_xboole_0
      | '#skF_1'(k4_orders_2('#skF_6','#skF_7'),k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_459,c_370])).

tff(c_495,plain,(
    ! [A_119] :
      ( r2_hidden(k1_xboole_0,A_119)
      | '#skF_1'(k4_orders_2('#skF_6','#skF_7'),k1_xboole_0) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_468])).

tff(c_505,plain,(
    '#skF_1'(k4_orders_2('#skF_6','#skF_7'),k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_495])).

tff(c_518,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | r1_tarski(k4_orders_2('#skF_6','#skF_7'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_4])).

tff(c_531,plain,(
    ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_518])).

tff(c_30,plain,(
    ! [A_41] :
      ( r2_hidden('#skF_5'(A_41),A_41)
      | k3_tarski(A_41) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_96,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_5'(A_63),B_64)
      | ~ r1_tarski(A_63,B_64)
      | k3_tarski(A_63) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_88])).

tff(c_10,plain,(
    ! [A_7,B_8] : ~ r2_hidden(A_7,k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_109,plain,(
    ! [A_65,B_66] :
      ( ~ r1_tarski(A_65,k2_zfmisc_1('#skF_5'(A_65),B_66))
      | k3_tarski(A_65) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_96,c_10])).

tff(c_119,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_109])).

tff(c_298,plain,(
    ! [B_93,A_94,C_95] :
      ( r2_hidden(k1_funct_1(B_93,u1_struct_0(A_94)),C_95)
      | ~ m2_orders_2(C_95,A_94,B_93)
      | ~ m1_orders_1(B_93,k1_orders_1(u1_struct_0(A_94)))
      | ~ l1_orders_2(A_94)
      | ~ v5_orders_2(A_94)
      | ~ v4_orders_2(A_94)
      | ~ v3_orders_2(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1405,plain,(
    ! [C_183,B_184,A_185] :
      ( k3_tarski(C_183) != k1_xboole_0
      | k1_funct_1(B_184,u1_struct_0(A_185)) = k1_xboole_0
      | ~ m2_orders_2(C_183,A_185,B_184)
      | ~ m1_orders_1(B_184,k1_orders_1(u1_struct_0(A_185)))
      | ~ l1_orders_2(A_185)
      | ~ v5_orders_2(A_185)
      | ~ v4_orders_2(A_185)
      | ~ v3_orders_2(A_185)
      | v2_struct_0(A_185) ) ),
    inference(resolution,[status(thm)],[c_298,c_28])).

tff(c_1413,plain,
    ( k3_tarski(k1_xboole_0) != k1_xboole_0
    | k1_funct_1('#skF_7',u1_struct_0('#skF_6')) = k1_xboole_0
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_277,c_1405])).

tff(c_1428,plain,
    ( k1_funct_1('#skF_7',u1_struct_0('#skF_6')) = k1_xboole_0
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_119,c_1413])).

tff(c_1429,plain,(
    k1_funct_1('#skF_7',u1_struct_0('#skF_6')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1428])).

tff(c_26,plain,(
    ! [B_38,A_34,C_40] :
      ( r2_hidden(k1_funct_1(B_38,u1_struct_0(A_34)),C_40)
      | ~ m2_orders_2(C_40,A_34,B_38)
      | ~ m1_orders_1(B_38,k1_orders_1(u1_struct_0(A_34)))
      | ~ l1_orders_2(A_34)
      | ~ v5_orders_2(A_34)
      | ~ v4_orders_2(A_34)
      | ~ v3_orders_2(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1436,plain,(
    ! [C_40] :
      ( r2_hidden(k1_xboole_0,C_40)
      | ~ m2_orders_2(C_40,'#skF_6','#skF_7')
      | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1429,c_26])).

tff(c_1443,plain,(
    ! [C_40] :
      ( r2_hidden(k1_xboole_0,C_40)
      | ~ m2_orders_2(C_40,'#skF_6','#skF_7')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_1436])).

tff(c_1447,plain,(
    ! [C_187] :
      ( r2_hidden(k1_xboole_0,C_187)
      | ~ m2_orders_2(C_187,'#skF_6','#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1443])).

tff(c_1459,plain,(
    r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_277,c_1447])).

tff(c_1466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_531,c_1459])).

tff(c_1468,plain,(
    r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_518])).

tff(c_1471,plain,(
    ! [B_2] :
      ( r2_hidden(k1_xboole_0,B_2)
      | ~ r1_tarski(k1_xboole_0,B_2) ) ),
    inference(resolution,[status(thm)],[c_1468,c_2])).

tff(c_1486,plain,(
    ! [B_190] : r2_hidden(k1_xboole_0,B_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1471])).

tff(c_1504,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_1486,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.57  
% 3.52/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.57  %$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.52/1.57  
% 3.52/1.57  %Foreground sorts:
% 3.52/1.57  
% 3.52/1.57  
% 3.52/1.57  %Background operators:
% 3.52/1.57  
% 3.52/1.57  
% 3.52/1.57  %Foreground operators:
% 3.52/1.57  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 3.52/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.52/1.57  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.52/1.57  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.52/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.52/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.57  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.52/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.52/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.57  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.52/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.52/1.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.52/1.57  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.52/1.57  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.52/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.52/1.57  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.52/1.57  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.52/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.52/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.52/1.57  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.52/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.52/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.52/1.57  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.52/1.57  
% 3.52/1.59  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.52/1.59  tff(f_132, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 3.52/1.59  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.52/1.59  tff(f_114, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 3.52/1.59  tff(f_75, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 3.52/1.59  tff(f_59, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 3.52/1.59  tff(f_37, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.52/1.59  tff(f_94, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 3.52/1.59  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.52/1.59  tff(c_34, plain, (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.52/1.59  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.52/1.59  tff(c_79, plain, (![A_56, B_57]: (k3_tarski(A_56)!=k1_xboole_0 | ~r2_hidden(B_57, A_56) | k1_xboole_0=B_57)), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.52/1.59  tff(c_86, plain, (![A_1, B_2]: (k3_tarski(A_1)!=k1_xboole_0 | '#skF_1'(A_1, B_2)=k1_xboole_0 | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_79])).
% 3.52/1.59  tff(c_88, plain, (![C_58, B_59, A_60]: (r2_hidden(C_58, B_59) | ~r2_hidden(C_58, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.52/1.59  tff(c_139, plain, (![A_69, B_70, B_71]: (r2_hidden('#skF_1'(A_69, B_70), B_71) | ~r1_tarski(A_69, B_71) | r1_tarski(A_69, B_70))), inference(resolution, [status(thm)], [c_6, c_88])).
% 3.52/1.59  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.52/1.59  tff(c_389, plain, (![A_104, B_105, B_106, B_107]: (r2_hidden('#skF_1'(A_104, B_105), B_106) | ~r1_tarski(B_107, B_106) | ~r1_tarski(A_104, B_107) | r1_tarski(A_104, B_105))), inference(resolution, [status(thm)], [c_139, c_2])).
% 3.52/1.59  tff(c_404, plain, (![A_111, B_112, A_113]: (r2_hidden('#skF_1'(A_111, B_112), A_113) | ~r1_tarski(A_111, k1_xboole_0) | r1_tarski(A_111, B_112))), inference(resolution, [status(thm)], [c_8, c_389])).
% 3.52/1.59  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.52/1.59  tff(c_428, plain, (![A_114, A_115]: (~r1_tarski(A_114, k1_xboole_0) | r1_tarski(A_114, A_115))), inference(resolution, [status(thm)], [c_404, c_4])).
% 3.52/1.59  tff(c_459, plain, (![A_118, A_119]: (r1_tarski(A_118, A_119) | k3_tarski(A_118)!=k1_xboole_0 | '#skF_1'(A_118, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_86, c_428])).
% 3.52/1.59  tff(c_46, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.52/1.59  tff(c_44, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.52/1.59  tff(c_42, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.52/1.59  tff(c_40, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.52/1.59  tff(c_38, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.52/1.59  tff(c_36, plain, (m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.52/1.59  tff(c_120, plain, (![A_67, B_68]: (m2_orders_2('#skF_4'(A_67, B_68), A_67, B_68) | ~m1_orders_1(B_68, k1_orders_1(u1_struct_0(A_67))) | ~l1_orders_2(A_67) | ~v5_orders_2(A_67) | ~v4_orders_2(A_67) | ~v3_orders_2(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.52/1.59  tff(c_122, plain, (m2_orders_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6', '#skF_7') | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_36, c_120])).
% 3.52/1.59  tff(c_125, plain, (m2_orders_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_122])).
% 3.52/1.59  tff(c_126, plain, (m2_orders_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_46, c_125])).
% 3.52/1.59  tff(c_244, plain, (![D_86, A_87, B_88]: (r2_hidden(D_86, k4_orders_2(A_87, B_88)) | ~m2_orders_2(D_86, A_87, B_88) | ~m1_orders_1(B_88, k1_orders_1(u1_struct_0(A_87))) | ~l1_orders_2(A_87) | ~v5_orders_2(A_87) | ~v4_orders_2(A_87) | ~v3_orders_2(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.52/1.59  tff(c_246, plain, (![D_86]: (r2_hidden(D_86, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_86, '#skF_6', '#skF_7') | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_36, c_244])).
% 3.52/1.59  tff(c_249, plain, (![D_86]: (r2_hidden(D_86, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_86, '#skF_6', '#skF_7') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_246])).
% 3.52/1.59  tff(c_251, plain, (![D_89]: (r2_hidden(D_89, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_89, '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_46, c_249])).
% 3.52/1.59  tff(c_28, plain, (![A_41, B_44]: (k3_tarski(A_41)!=k1_xboole_0 | ~r2_hidden(B_44, A_41) | k1_xboole_0=B_44)), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.52/1.59  tff(c_258, plain, (![D_89]: (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))!=k1_xboole_0 | k1_xboole_0=D_89 | ~m2_orders_2(D_89, '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_251, c_28])).
% 3.52/1.59  tff(c_272, plain, (![D_90]: (k1_xboole_0=D_90 | ~m2_orders_2(D_90, '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_258])).
% 3.52/1.59  tff(c_276, plain, ('#skF_4'('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_126, c_272])).
% 3.52/1.59  tff(c_277, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_126])).
% 3.52/1.59  tff(c_287, plain, (![D_91, B_92]: (r2_hidden(D_91, B_92) | ~r1_tarski(k4_orders_2('#skF_6', '#skF_7'), B_92) | ~m2_orders_2(D_91, '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_251, c_2])).
% 3.52/1.59  tff(c_290, plain, (![D_91, B_2]: (r2_hidden(D_91, B_2) | ~m2_orders_2(D_91, '#skF_6', '#skF_7') | k3_tarski(k4_orders_2('#skF_6', '#skF_7'))!=k1_xboole_0 | '#skF_1'(k4_orders_2('#skF_6', '#skF_7'), B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_86, c_287])).
% 3.52/1.59  tff(c_327, plain, (![D_100, B_101]: (r2_hidden(D_100, B_101) | ~m2_orders_2(D_100, '#skF_6', '#skF_7') | '#skF_1'(k4_orders_2('#skF_6', '#skF_7'), B_101)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_290])).
% 3.52/1.59  tff(c_331, plain, (![B_102]: (r2_hidden(k1_xboole_0, B_102) | '#skF_1'(k4_orders_2('#skF_6', '#skF_7'), B_102)=k1_xboole_0)), inference(resolution, [status(thm)], [c_277, c_327])).
% 3.52/1.59  tff(c_350, plain, (![B_102]: (r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7')) | r1_tarski(k4_orders_2('#skF_6', '#skF_7'), B_102) | r2_hidden(k1_xboole_0, B_102))), inference(superposition, [status(thm), theory('equality')], [c_331, c_6])).
% 3.52/1.59  tff(c_358, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_350])).
% 3.52/1.59  tff(c_370, plain, (![B_2]: (r2_hidden(k1_xboole_0, B_2) | ~r1_tarski(k4_orders_2('#skF_6', '#skF_7'), B_2))), inference(resolution, [status(thm)], [c_358, c_2])).
% 3.52/1.59  tff(c_468, plain, (![A_119]: (r2_hidden(k1_xboole_0, A_119) | k3_tarski(k4_orders_2('#skF_6', '#skF_7'))!=k1_xboole_0 | '#skF_1'(k4_orders_2('#skF_6', '#skF_7'), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_459, c_370])).
% 3.52/1.59  tff(c_495, plain, (![A_119]: (r2_hidden(k1_xboole_0, A_119) | '#skF_1'(k4_orders_2('#skF_6', '#skF_7'), k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_468])).
% 3.52/1.59  tff(c_505, plain, ('#skF_1'(k4_orders_2('#skF_6', '#skF_7'), k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_495])).
% 3.52/1.59  tff(c_518, plain, (~r2_hidden(k1_xboole_0, k1_xboole_0) | r1_tarski(k4_orders_2('#skF_6', '#skF_7'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_505, c_4])).
% 3.52/1.59  tff(c_531, plain, (~r2_hidden(k1_xboole_0, k1_xboole_0)), inference(splitLeft, [status(thm)], [c_518])).
% 3.52/1.59  tff(c_30, plain, (![A_41]: (r2_hidden('#skF_5'(A_41), A_41) | k3_tarski(A_41)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.52/1.59  tff(c_96, plain, (![A_63, B_64]: (r2_hidden('#skF_5'(A_63), B_64) | ~r1_tarski(A_63, B_64) | k3_tarski(A_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_88])).
% 3.52/1.59  tff(c_10, plain, (![A_7, B_8]: (~r2_hidden(A_7, k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.52/1.59  tff(c_109, plain, (![A_65, B_66]: (~r1_tarski(A_65, k2_zfmisc_1('#skF_5'(A_65), B_66)) | k3_tarski(A_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_96, c_10])).
% 3.52/1.59  tff(c_119, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_109])).
% 3.52/1.59  tff(c_298, plain, (![B_93, A_94, C_95]: (r2_hidden(k1_funct_1(B_93, u1_struct_0(A_94)), C_95) | ~m2_orders_2(C_95, A_94, B_93) | ~m1_orders_1(B_93, k1_orders_1(u1_struct_0(A_94))) | ~l1_orders_2(A_94) | ~v5_orders_2(A_94) | ~v4_orders_2(A_94) | ~v3_orders_2(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.52/1.59  tff(c_1405, plain, (![C_183, B_184, A_185]: (k3_tarski(C_183)!=k1_xboole_0 | k1_funct_1(B_184, u1_struct_0(A_185))=k1_xboole_0 | ~m2_orders_2(C_183, A_185, B_184) | ~m1_orders_1(B_184, k1_orders_1(u1_struct_0(A_185))) | ~l1_orders_2(A_185) | ~v5_orders_2(A_185) | ~v4_orders_2(A_185) | ~v3_orders_2(A_185) | v2_struct_0(A_185))), inference(resolution, [status(thm)], [c_298, c_28])).
% 3.52/1.59  tff(c_1413, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0 | k1_funct_1('#skF_7', u1_struct_0('#skF_6'))=k1_xboole_0 | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_277, c_1405])).
% 3.52/1.59  tff(c_1428, plain, (k1_funct_1('#skF_7', u1_struct_0('#skF_6'))=k1_xboole_0 | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_119, c_1413])).
% 3.52/1.59  tff(c_1429, plain, (k1_funct_1('#skF_7', u1_struct_0('#skF_6'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_46, c_1428])).
% 3.52/1.59  tff(c_26, plain, (![B_38, A_34, C_40]: (r2_hidden(k1_funct_1(B_38, u1_struct_0(A_34)), C_40) | ~m2_orders_2(C_40, A_34, B_38) | ~m1_orders_1(B_38, k1_orders_1(u1_struct_0(A_34))) | ~l1_orders_2(A_34) | ~v5_orders_2(A_34) | ~v4_orders_2(A_34) | ~v3_orders_2(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.52/1.59  tff(c_1436, plain, (![C_40]: (r2_hidden(k1_xboole_0, C_40) | ~m2_orders_2(C_40, '#skF_6', '#skF_7') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1429, c_26])).
% 3.52/1.59  tff(c_1443, plain, (![C_40]: (r2_hidden(k1_xboole_0, C_40) | ~m2_orders_2(C_40, '#skF_6', '#skF_7') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_1436])).
% 3.52/1.59  tff(c_1447, plain, (![C_187]: (r2_hidden(k1_xboole_0, C_187) | ~m2_orders_2(C_187, '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_46, c_1443])).
% 3.52/1.59  tff(c_1459, plain, (r2_hidden(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_277, c_1447])).
% 3.52/1.59  tff(c_1466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_531, c_1459])).
% 3.52/1.59  tff(c_1468, plain, (r2_hidden(k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_518])).
% 3.52/1.59  tff(c_1471, plain, (![B_2]: (r2_hidden(k1_xboole_0, B_2) | ~r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_1468, c_2])).
% 3.52/1.59  tff(c_1486, plain, (![B_190]: (r2_hidden(k1_xboole_0, B_190))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1471])).
% 3.52/1.59  tff(c_1504, plain, $false, inference(resolution, [status(thm)], [c_1486, c_10])).
% 3.52/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.59  
% 3.52/1.59  Inference rules
% 3.52/1.59  ----------------------
% 3.52/1.59  #Ref     : 0
% 3.52/1.59  #Sup     : 322
% 3.52/1.59  #Fact    : 0
% 3.52/1.59  #Define  : 0
% 3.52/1.59  #Split   : 6
% 3.52/1.59  #Chain   : 0
% 3.52/1.59  #Close   : 0
% 3.52/1.59  
% 3.52/1.59  Ordering : KBO
% 3.52/1.59  
% 3.52/1.59  Simplification rules
% 3.52/1.59  ----------------------
% 3.52/1.59  #Subsume      : 73
% 3.52/1.59  #Demod        : 207
% 3.52/1.59  #Tautology    : 146
% 3.52/1.59  #SimpNegUnit  : 39
% 3.52/1.59  #BackRed      : 19
% 3.52/1.59  
% 3.52/1.59  #Partial instantiations: 0
% 3.52/1.59  #Strategies tried      : 1
% 3.52/1.59  
% 3.52/1.59  Timing (in seconds)
% 3.52/1.59  ----------------------
% 3.52/1.59  Preprocessing        : 0.32
% 3.52/1.59  Parsing              : 0.17
% 3.52/1.59  CNF conversion       : 0.03
% 3.52/1.59  Main loop            : 0.51
% 3.52/1.59  Inferencing          : 0.18
% 3.52/1.59  Reduction            : 0.15
% 3.52/1.59  Demodulation         : 0.10
% 3.52/1.59  BG Simplification    : 0.02
% 3.52/1.59  Subsumption          : 0.12
% 3.52/1.59  Abstraction          : 0.02
% 3.52/1.59  MUC search           : 0.00
% 3.52/1.59  Cooper               : 0.00
% 3.52/1.59  Total                : 0.87
% 3.52/1.59  Index Insertion      : 0.00
% 3.52/1.59  Index Deletion       : 0.00
% 3.52/1.59  Index Matching       : 0.00
% 3.52/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
