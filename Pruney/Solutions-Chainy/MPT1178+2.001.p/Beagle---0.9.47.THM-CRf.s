%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:02 EST 2020

% Result     : Theorem 4.86s
% Output     : CNFRefutation 5.17s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 191 expanded)
%              Number of leaves         :   46 (  96 expanded)
%              Depth                    :   18
%              Number of atoms          :  152 ( 599 expanded)
%              Number of equality atoms :   24 (  72 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k4_xboole_0 > k4_orders_2 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_175,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => m2_orders_2(k1_tarski(k1_funct_1(B,u1_struct_0(A))),A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_orders_2)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_102,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_157,axiom,(
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
             => ! [D] :
                  ( m2_orders_2(D,A,B)
                 => ~ r1_xboole_0(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_125,plain,(
    ! [B_83,A_84] : k2_xboole_0(B_83,A_84) = k2_xboole_0(A_84,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_141,plain,(
    ! [A_84] : k2_xboole_0(k1_xboole_0,A_84) = A_84 ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_4])).

tff(c_228,plain,(
    ! [A_92,B_93] : k4_xboole_0(k2_xboole_0(A_92,B_93),B_93) = k4_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_237,plain,(
    ! [A_84] : k4_xboole_0(k1_xboole_0,A_84) = k4_xboole_0(A_84,A_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_228])).

tff(c_249,plain,(
    ! [A_84] : k4_xboole_0(A_84,A_84) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_237])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_66,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_64,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_62,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_60,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_58,plain,(
    m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_52,plain,(
    ! [B_54,A_52] :
      ( m2_orders_2(k1_tarski(k1_funct_1(B_54,u1_struct_0(A_52))),A_52,B_54)
      | ~ m1_orders_1(B_54,k1_orders_1(u1_struct_0(A_52)))
      | ~ l1_orders_2(A_52)
      | ~ v5_orders_2(A_52)
      | ~ v4_orders_2(A_52)
      | ~ v3_orders_2(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_6,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    k3_tarski(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1509,plain,(
    ! [D_142,A_143,B_144] :
      ( r2_hidden(D_142,k4_orders_2(A_143,B_144))
      | ~ m2_orders_2(D_142,A_143,B_144)
      | ~ m1_orders_1(B_144,k1_orders_1(u1_struct_0(A_143)))
      | ~ l1_orders_2(A_143)
      | ~ v5_orders_2(A_143)
      | ~ v4_orders_2(A_143)
      | ~ v3_orders_2(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1511,plain,(
    ! [D_142] :
      ( r2_hidden(D_142,k4_orders_2('#skF_4','#skF_5'))
      | ~ m2_orders_2(D_142,'#skF_4','#skF_5')
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_1509])).

tff(c_1514,plain,(
    ! [D_142] :
      ( r2_hidden(D_142,k4_orders_2('#skF_4','#skF_5'))
      | ~ m2_orders_2(D_142,'#skF_4','#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_1511])).

tff(c_1518,plain,(
    ! [D_145] :
      ( r2_hidden(D_145,k4_orders_2('#skF_4','#skF_5'))
      | ~ m2_orders_2(D_145,'#skF_4','#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1514])).

tff(c_28,plain,(
    ! [C_21,B_20,A_19] :
      ( r1_tarski(C_21,B_20)
      | ~ r2_hidden(C_21,A_19)
      | ~ r1_tarski(k3_tarski(A_19),B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1522,plain,(
    ! [D_145,B_20] :
      ( r1_tarski(D_145,B_20)
      | ~ r1_tarski(k3_tarski(k4_orders_2('#skF_4','#skF_5')),B_20)
      | ~ m2_orders_2(D_145,'#skF_4','#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1518,c_28])).

tff(c_1530,plain,(
    ! [D_146,B_147] :
      ( r1_tarski(D_146,B_147)
      | ~ m2_orders_2(D_146,'#skF_4','#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_56,c_1522])).

tff(c_1533,plain,(
    ! [B_147] :
      ( r1_tarski(k1_tarski(k1_funct_1('#skF_5',u1_struct_0('#skF_4'))),B_147)
      | ~ m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_1530])).

tff(c_1536,plain,(
    ! [B_147] :
      ( r1_tarski(k1_tarski(k1_funct_1('#skF_5',u1_struct_0('#skF_4'))),B_147)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_1533])).

tff(c_1538,plain,(
    ! [B_148] : r1_tarski(k1_tarski(k1_funct_1('#skF_5',u1_struct_0('#skF_4'))),B_148) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1536])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1543,plain,(
    k1_tarski(k1_funct_1('#skF_5',u1_struct_0('#skF_4'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1538,c_8])).

tff(c_1549,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_4','#skF_5')
    | ~ m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1543,c_52])).

tff(c_1553,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_1549])).

tff(c_1554,plain,(
    m2_orders_2(k1_xboole_0,'#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1553])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1857,plain,(
    ! [C_153,D_154,A_155,B_156] :
      ( ~ r1_xboole_0(C_153,D_154)
      | ~ m2_orders_2(D_154,A_155,B_156)
      | ~ m2_orders_2(C_153,A_155,B_156)
      | ~ m1_orders_1(B_156,k1_orders_1(u1_struct_0(A_155)))
      | ~ l1_orders_2(A_155)
      | ~ v5_orders_2(A_155)
      | ~ v4_orders_2(A_155)
      | ~ v3_orders_2(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_3201,plain,(
    ! [B_211,A_212,B_213,A_214] :
      ( ~ m2_orders_2(B_211,A_212,B_213)
      | ~ m2_orders_2(A_214,A_212,B_213)
      | ~ m1_orders_1(B_213,k1_orders_1(u1_struct_0(A_212)))
      | ~ l1_orders_2(A_212)
      | ~ v5_orders_2(A_212)
      | ~ v4_orders_2(A_212)
      | ~ v3_orders_2(A_212)
      | v2_struct_0(A_212)
      | k4_xboole_0(A_214,B_211) != A_214 ) ),
    inference(resolution,[status(thm)],[c_18,c_1857])).

tff(c_3207,plain,(
    ! [A_214] :
      ( ~ m2_orders_2(A_214,'#skF_4','#skF_5')
      | ~ m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | k4_xboole_0(A_214,k1_xboole_0) != A_214 ) ),
    inference(resolution,[status(thm)],[c_1554,c_3201])).

tff(c_3220,plain,(
    ! [A_214] :
      ( ~ m2_orders_2(A_214,'#skF_4','#skF_5')
      | v2_struct_0('#skF_4')
      | k4_xboole_0(A_214,k1_xboole_0) != A_214 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_3207])).

tff(c_3223,plain,(
    ! [A_215] :
      ( ~ m2_orders_2(A_215,'#skF_4','#skF_5')
      | k4_xboole_0(A_215,k1_xboole_0) != A_215 ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3220])).

tff(c_3232,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1554,c_3223])).

tff(c_3242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_3232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:43:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.86/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/1.99  
% 5.17/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/1.99  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k4_xboole_0 > k4_orders_2 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.17/1.99  
% 5.17/1.99  %Foreground sorts:
% 5.17/1.99  
% 5.17/1.99  
% 5.17/1.99  %Background operators:
% 5.17/1.99  
% 5.17/1.99  
% 5.17/1.99  %Foreground operators:
% 5.17/1.99  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 5.17/1.99  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.17/1.99  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.17/1.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.17/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.17/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.17/1.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.17/1.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.17/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.17/1.99  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 5.17/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.17/1.99  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 5.17/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.17/1.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.17/1.99  tff('#skF_5', type, '#skF_5': $i).
% 5.17/1.99  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.17/1.99  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.17/1.99  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.17/1.99  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.17/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.17/1.99  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.17/1.99  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.17/1.99  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 5.17/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.17/1.99  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.17/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.17/1.99  tff('#skF_4', type, '#skF_4': $i).
% 5.17/1.99  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.17/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.17/1.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.17/1.99  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.17/1.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.17/1.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.17/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.17/1.99  
% 5.17/2.01  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 5.17/2.01  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.17/2.01  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.17/2.01  tff(f_37, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 5.17/2.01  tff(f_175, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 5.17/2.01  tff(f_134, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => m2_orders_2(k1_tarski(k1_funct_1(B, u1_struct_0(A))), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_orders_2)).
% 5.17/2.01  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.17/2.01  tff(f_102, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 5.17/2.01  tff(f_67, axiom, (![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 5.17/2.01  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.17/2.01  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.17/2.01  tff(f_157, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 5.17/2.01  tff(c_12, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.17/2.01  tff(c_125, plain, (![B_83, A_84]: (k2_xboole_0(B_83, A_84)=k2_xboole_0(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.17/2.01  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.17/2.01  tff(c_141, plain, (![A_84]: (k2_xboole_0(k1_xboole_0, A_84)=A_84)), inference(superposition, [status(thm), theory('equality')], [c_125, c_4])).
% 5.17/2.01  tff(c_228, plain, (![A_92, B_93]: (k4_xboole_0(k2_xboole_0(A_92, B_93), B_93)=k4_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.17/2.01  tff(c_237, plain, (![A_84]: (k4_xboole_0(k1_xboole_0, A_84)=k4_xboole_0(A_84, A_84))), inference(superposition, [status(thm), theory('equality')], [c_141, c_228])).
% 5.17/2.01  tff(c_249, plain, (![A_84]: (k4_xboole_0(A_84, A_84)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_237])).
% 5.17/2.01  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.17/2.01  tff(c_66, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.17/2.01  tff(c_64, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.17/2.01  tff(c_62, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.17/2.01  tff(c_60, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.17/2.01  tff(c_58, plain, (m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.17/2.01  tff(c_52, plain, (![B_54, A_52]: (m2_orders_2(k1_tarski(k1_funct_1(B_54, u1_struct_0(A_52))), A_52, B_54) | ~m1_orders_1(B_54, k1_orders_1(u1_struct_0(A_52))) | ~l1_orders_2(A_52) | ~v5_orders_2(A_52) | ~v4_orders_2(A_52) | ~v3_orders_2(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.17/2.01  tff(c_6, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.17/2.01  tff(c_56, plain, (k3_tarski(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.17/2.01  tff(c_1509, plain, (![D_142, A_143, B_144]: (r2_hidden(D_142, k4_orders_2(A_143, B_144)) | ~m2_orders_2(D_142, A_143, B_144) | ~m1_orders_1(B_144, k1_orders_1(u1_struct_0(A_143))) | ~l1_orders_2(A_143) | ~v5_orders_2(A_143) | ~v4_orders_2(A_143) | ~v3_orders_2(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.17/2.01  tff(c_1511, plain, (![D_142]: (r2_hidden(D_142, k4_orders_2('#skF_4', '#skF_5')) | ~m2_orders_2(D_142, '#skF_4', '#skF_5') | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_1509])).
% 5.17/2.01  tff(c_1514, plain, (![D_142]: (r2_hidden(D_142, k4_orders_2('#skF_4', '#skF_5')) | ~m2_orders_2(D_142, '#skF_4', '#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_1511])).
% 5.17/2.01  tff(c_1518, plain, (![D_145]: (r2_hidden(D_145, k4_orders_2('#skF_4', '#skF_5')) | ~m2_orders_2(D_145, '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_68, c_1514])).
% 5.17/2.01  tff(c_28, plain, (![C_21, B_20, A_19]: (r1_tarski(C_21, B_20) | ~r2_hidden(C_21, A_19) | ~r1_tarski(k3_tarski(A_19), B_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.17/2.01  tff(c_1522, plain, (![D_145, B_20]: (r1_tarski(D_145, B_20) | ~r1_tarski(k3_tarski(k4_orders_2('#skF_4', '#skF_5')), B_20) | ~m2_orders_2(D_145, '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1518, c_28])).
% 5.17/2.01  tff(c_1530, plain, (![D_146, B_147]: (r1_tarski(D_146, B_147) | ~m2_orders_2(D_146, '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_56, c_1522])).
% 5.17/2.01  tff(c_1533, plain, (![B_147]: (r1_tarski(k1_tarski(k1_funct_1('#skF_5', u1_struct_0('#skF_4'))), B_147) | ~m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_1530])).
% 5.17/2.01  tff(c_1536, plain, (![B_147]: (r1_tarski(k1_tarski(k1_funct_1('#skF_5', u1_struct_0('#skF_4'))), B_147) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_1533])).
% 5.17/2.01  tff(c_1538, plain, (![B_148]: (r1_tarski(k1_tarski(k1_funct_1('#skF_5', u1_struct_0('#skF_4'))), B_148))), inference(negUnitSimplification, [status(thm)], [c_68, c_1536])).
% 5.17/2.01  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.17/2.01  tff(c_1543, plain, (k1_tarski(k1_funct_1('#skF_5', u1_struct_0('#skF_4')))=k1_xboole_0), inference(resolution, [status(thm)], [c_1538, c_8])).
% 5.17/2.01  tff(c_1549, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5') | ~m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1543, c_52])).
% 5.17/2.01  tff(c_1553, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_1549])).
% 5.17/2.01  tff(c_1554, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_1553])).
% 5.17/2.01  tff(c_18, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k4_xboole_0(A_12, B_13)!=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.17/2.01  tff(c_1857, plain, (![C_153, D_154, A_155, B_156]: (~r1_xboole_0(C_153, D_154) | ~m2_orders_2(D_154, A_155, B_156) | ~m2_orders_2(C_153, A_155, B_156) | ~m1_orders_1(B_156, k1_orders_1(u1_struct_0(A_155))) | ~l1_orders_2(A_155) | ~v5_orders_2(A_155) | ~v4_orders_2(A_155) | ~v3_orders_2(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.17/2.01  tff(c_3201, plain, (![B_211, A_212, B_213, A_214]: (~m2_orders_2(B_211, A_212, B_213) | ~m2_orders_2(A_214, A_212, B_213) | ~m1_orders_1(B_213, k1_orders_1(u1_struct_0(A_212))) | ~l1_orders_2(A_212) | ~v5_orders_2(A_212) | ~v4_orders_2(A_212) | ~v3_orders_2(A_212) | v2_struct_0(A_212) | k4_xboole_0(A_214, B_211)!=A_214)), inference(resolution, [status(thm)], [c_18, c_1857])).
% 5.17/2.01  tff(c_3207, plain, (![A_214]: (~m2_orders_2(A_214, '#skF_4', '#skF_5') | ~m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | k4_xboole_0(A_214, k1_xboole_0)!=A_214)), inference(resolution, [status(thm)], [c_1554, c_3201])).
% 5.17/2.01  tff(c_3220, plain, (![A_214]: (~m2_orders_2(A_214, '#skF_4', '#skF_5') | v2_struct_0('#skF_4') | k4_xboole_0(A_214, k1_xboole_0)!=A_214)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_3207])).
% 5.17/2.01  tff(c_3223, plain, (![A_215]: (~m2_orders_2(A_215, '#skF_4', '#skF_5') | k4_xboole_0(A_215, k1_xboole_0)!=A_215)), inference(negUnitSimplification, [status(thm)], [c_68, c_3220])).
% 5.17/2.01  tff(c_3232, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_1554, c_3223])).
% 5.17/2.01  tff(c_3242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_249, c_3232])).
% 5.17/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/2.01  
% 5.17/2.01  Inference rules
% 5.17/2.01  ----------------------
% 5.17/2.01  #Ref     : 0
% 5.17/2.01  #Sup     : 807
% 5.17/2.01  #Fact    : 0
% 5.17/2.01  #Define  : 0
% 5.17/2.01  #Split   : 1
% 5.17/2.01  #Chain   : 0
% 5.17/2.01  #Close   : 0
% 5.17/2.01  
% 5.17/2.01  Ordering : KBO
% 5.17/2.01  
% 5.17/2.01  Simplification rules
% 5.17/2.01  ----------------------
% 5.17/2.01  #Subsume      : 37
% 5.17/2.01  #Demod        : 605
% 5.17/2.01  #Tautology    : 405
% 5.17/2.01  #SimpNegUnit  : 17
% 5.17/2.01  #BackRed      : 3
% 5.17/2.01  
% 5.17/2.01  #Partial instantiations: 0
% 5.17/2.01  #Strategies tried      : 1
% 5.17/2.01  
% 5.17/2.01  Timing (in seconds)
% 5.17/2.01  ----------------------
% 5.17/2.01  Preprocessing        : 0.36
% 5.17/2.01  Parsing              : 0.20
% 5.17/2.01  CNF conversion       : 0.03
% 5.17/2.01  Main loop            : 0.82
% 5.17/2.01  Inferencing          : 0.21
% 5.17/2.01  Reduction            : 0.39
% 5.17/2.01  Demodulation         : 0.33
% 5.17/2.01  BG Simplification    : 0.03
% 5.17/2.01  Subsumption          : 0.14
% 5.17/2.01  Abstraction          : 0.04
% 5.17/2.01  MUC search           : 0.00
% 5.17/2.01  Cooper               : 0.00
% 5.17/2.01  Total                : 1.22
% 5.17/2.01  Index Insertion      : 0.00
% 5.17/2.01  Index Deletion       : 0.00
% 5.17/2.01  Index Matching       : 0.00
% 5.17/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
