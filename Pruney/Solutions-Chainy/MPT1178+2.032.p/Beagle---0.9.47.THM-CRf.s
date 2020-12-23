%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:06 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 232 expanded)
%              Number of leaves         :   40 ( 106 expanded)
%              Depth                    :   17
%              Number of atoms          :  175 ( 746 expanded)
%              Number of equality atoms :   22 ( 168 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3

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

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_wellord1,type,(
    r2_wellord1: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_145,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_89,axiom,(
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

tff(f_109,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_orders_2(C,A,B)
         => ( v6_orders_2(C,A)
            & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v6_orders_2(C,A)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
             => ( m2_orders_2(C,A,B)
              <=> ( C != k1_xboole_0
                  & r2_wellord1(u1_orders_2(A),C)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_hidden(D,C)
                       => k1_funct_1(B,k1_orders_2(A,k3_orders_2(A,C,D))) = D ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_orders_2)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_52,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_50,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_48,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_46,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_44,plain,(
    m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_42,plain,(
    k3_tarski(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_78,plain,(
    ! [A_61,B_62] :
      ( k3_tarski(A_61) != k1_xboole_0
      | ~ r2_hidden(B_62,A_61)
      | k1_xboole_0 = B_62 ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_87,plain,(
    ! [A_63] :
      ( k3_tarski(A_63) != k1_xboole_0
      | '#skF_1'(A_63) = k1_xboole_0
      | k1_xboole_0 = A_63 ) ),
    inference(resolution,[status(thm)],[c_4,c_78])).

tff(c_95,plain,
    ( '#skF_1'(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0
    | k4_orders_2('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_87])).

tff(c_97,plain,(
    k4_orders_2('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_98,plain,(
    ! [A_65,B_66] :
      ( ~ v1_xboole_0(k4_orders_2(A_65,B_66))
      | ~ m1_orders_1(B_66,k1_orders_1(u1_struct_0(A_65)))
      | ~ l1_orders_2(A_65)
      | ~ v5_orders_2(A_65)
      | ~ v4_orders_2(A_65)
      | ~ v3_orders_2(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_101,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7'))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_98])).

tff(c_104,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_101])).

tff(c_105,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_104])).

tff(c_106,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_105])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_106])).

tff(c_112,plain,(
    k4_orders_2('#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_111,plain,(
    '#skF_1'(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_116,plain,
    ( r2_hidden(k1_xboole_0,k4_orders_2('#skF_6','#skF_7'))
    | k4_orders_2('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_4])).

tff(c_119,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_116])).

tff(c_138,plain,(
    ! [D_75,A_76,B_77] :
      ( m2_orders_2(D_75,A_76,B_77)
      | ~ r2_hidden(D_75,k4_orders_2(A_76,B_77))
      | ~ m1_orders_1(B_77,k1_orders_1(u1_struct_0(A_76)))
      | ~ l1_orders_2(A_76)
      | ~ v5_orders_2(A_76)
      | ~ v4_orders_2(A_76)
      | ~ v3_orders_2(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_140,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_119,c_138])).

tff(c_149,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_140])).

tff(c_150,plain,(
    m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_149])).

tff(c_32,plain,(
    ! [C_50,A_47,B_48] :
      ( v6_orders_2(C_50,A_47)
      | ~ m2_orders_2(C_50,A_47,B_48)
      | ~ m1_orders_1(B_48,k1_orders_1(u1_struct_0(A_47)))
      | ~ l1_orders_2(A_47)
      | ~ v5_orders_2(A_47)
      | ~ v4_orders_2(A_47)
      | ~ v3_orders_2(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_156,plain,
    ( v6_orders_2(k1_xboole_0,'#skF_6')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_150,c_32])).

tff(c_163,plain,
    ( v6_orders_2(k1_xboole_0,'#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_156])).

tff(c_164,plain,(
    v6_orders_2(k1_xboole_0,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_163])).

tff(c_30,plain,(
    ! [C_50,A_47,B_48] :
      ( m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m2_orders_2(C_50,A_47,B_48)
      | ~ m1_orders_1(B_48,k1_orders_1(u1_struct_0(A_47)))
      | ~ l1_orders_2(A_47)
      | ~ v5_orders_2(A_47)
      | ~ v4_orders_2(A_47)
      | ~ v3_orders_2(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_154,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_150,c_30])).

tff(c_159,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_154])).

tff(c_160,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_159])).

tff(c_219,plain,(
    ! [A_87,B_88] :
      ( ~ m2_orders_2(k1_xboole_0,A_87,B_88)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ v6_orders_2(k1_xboole_0,A_87)
      | ~ m1_orders_1(B_88,k1_orders_1(u1_struct_0(A_87)))
      | ~ l1_orders_2(A_87)
      | ~ v5_orders_2(A_87)
      | ~ v4_orders_2(A_87)
      | ~ v3_orders_2(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_221,plain,(
    ! [B_88] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_6',B_88)
      | ~ v6_orders_2(k1_xboole_0,'#skF_6')
      | ~ m1_orders_1(B_88,k1_orders_1(u1_struct_0('#skF_6')))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_160,c_219])).

tff(c_224,plain,(
    ! [B_88] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_6',B_88)
      | ~ m1_orders_1(B_88,k1_orders_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_164,c_221])).

tff(c_236,plain,(
    ! [B_92] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_6',B_92)
      | ~ m1_orders_1(B_92,k1_orders_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_224])).

tff(c_239,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_236])).

tff(c_243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:31:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.35  
% 2.36/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.35  %$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3
% 2.36/1.35  
% 2.36/1.35  %Foreground sorts:
% 2.36/1.35  
% 2.36/1.35  
% 2.36/1.35  %Background operators:
% 2.36/1.35  
% 2.36/1.35  
% 2.36/1.35  %Foreground operators:
% 2.36/1.35  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.36/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.36/1.35  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.36/1.35  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.36/1.35  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.36/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.36/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.35  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.36/1.35  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.36/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.36/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.36/1.35  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.36/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.36/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.36/1.35  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.36/1.35  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.36/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.35  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.36/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.36/1.35  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.36/1.35  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.36/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.36/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.36/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.35  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.36/1.35  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.36/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.36/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.36/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.35  
% 2.53/1.37  tff(f_163, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.53/1.37  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.53/1.37  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.53/1.37  tff(f_145, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 2.53/1.37  tff(f_125, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.53/1.37  tff(f_89, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.53/1.37  tff(f_109, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.53/1.37  tff(f_67, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => (m2_orders_2(C, A, B) <=> ((~(C = k1_xboole_0) & r2_wellord1(u1_orders_2(A), C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => (k1_funct_1(B, k1_orders_2(A, k3_orders_2(A, C, D))) = D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_orders_2)).
% 2.53/1.37  tff(c_54, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.53/1.37  tff(c_52, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.53/1.37  tff(c_50, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.53/1.37  tff(c_48, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.53/1.37  tff(c_46, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.53/1.37  tff(c_44, plain, (m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.53/1.37  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.53/1.37  tff(c_42, plain, (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.53/1.37  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.53/1.37  tff(c_78, plain, (![A_61, B_62]: (k3_tarski(A_61)!=k1_xboole_0 | ~r2_hidden(B_62, A_61) | k1_xboole_0=B_62)), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.53/1.37  tff(c_87, plain, (![A_63]: (k3_tarski(A_63)!=k1_xboole_0 | '#skF_1'(A_63)=k1_xboole_0 | k1_xboole_0=A_63)), inference(resolution, [status(thm)], [c_4, c_78])).
% 2.53/1.37  tff(c_95, plain, ('#skF_1'(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0 | k4_orders_2('#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_42, c_87])).
% 2.53/1.37  tff(c_97, plain, (k4_orders_2('#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_95])).
% 2.53/1.37  tff(c_98, plain, (![A_65, B_66]: (~v1_xboole_0(k4_orders_2(A_65, B_66)) | ~m1_orders_1(B_66, k1_orders_1(u1_struct_0(A_65))) | ~l1_orders_2(A_65) | ~v5_orders_2(A_65) | ~v4_orders_2(A_65) | ~v3_orders_2(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.53/1.37  tff(c_101, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_44, c_98])).
% 2.53/1.37  tff(c_104, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_101])).
% 2.53/1.37  tff(c_105, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_54, c_104])).
% 2.53/1.37  tff(c_106, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_97, c_105])).
% 2.53/1.37  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_106])).
% 2.53/1.37  tff(c_112, plain, (k4_orders_2('#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_95])).
% 2.53/1.37  tff(c_111, plain, ('#skF_1'(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_95])).
% 2.53/1.37  tff(c_116, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7')) | k4_orders_2('#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_111, c_4])).
% 2.53/1.37  tff(c_119, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_112, c_116])).
% 2.53/1.37  tff(c_138, plain, (![D_75, A_76, B_77]: (m2_orders_2(D_75, A_76, B_77) | ~r2_hidden(D_75, k4_orders_2(A_76, B_77)) | ~m1_orders_1(B_77, k1_orders_1(u1_struct_0(A_76))) | ~l1_orders_2(A_76) | ~v5_orders_2(A_76) | ~v4_orders_2(A_76) | ~v3_orders_2(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.53/1.37  tff(c_140, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_119, c_138])).
% 2.53/1.37  tff(c_149, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_140])).
% 2.53/1.37  tff(c_150, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_54, c_149])).
% 2.53/1.37  tff(c_32, plain, (![C_50, A_47, B_48]: (v6_orders_2(C_50, A_47) | ~m2_orders_2(C_50, A_47, B_48) | ~m1_orders_1(B_48, k1_orders_1(u1_struct_0(A_47))) | ~l1_orders_2(A_47) | ~v5_orders_2(A_47) | ~v4_orders_2(A_47) | ~v3_orders_2(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.53/1.37  tff(c_156, plain, (v6_orders_2(k1_xboole_0, '#skF_6') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_150, c_32])).
% 2.53/1.37  tff(c_163, plain, (v6_orders_2(k1_xboole_0, '#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_156])).
% 2.53/1.37  tff(c_164, plain, (v6_orders_2(k1_xboole_0, '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_54, c_163])).
% 2.53/1.37  tff(c_30, plain, (![C_50, A_47, B_48]: (m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_47))) | ~m2_orders_2(C_50, A_47, B_48) | ~m1_orders_1(B_48, k1_orders_1(u1_struct_0(A_47))) | ~l1_orders_2(A_47) | ~v5_orders_2(A_47) | ~v4_orders_2(A_47) | ~v3_orders_2(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.53/1.37  tff(c_154, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_150, c_30])).
% 2.53/1.37  tff(c_159, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_154])).
% 2.53/1.37  tff(c_160, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_54, c_159])).
% 2.53/1.37  tff(c_219, plain, (![A_87, B_88]: (~m2_orders_2(k1_xboole_0, A_87, B_88) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_87))) | ~v6_orders_2(k1_xboole_0, A_87) | ~m1_orders_1(B_88, k1_orders_1(u1_struct_0(A_87))) | ~l1_orders_2(A_87) | ~v5_orders_2(A_87) | ~v4_orders_2(A_87) | ~v3_orders_2(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.53/1.37  tff(c_221, plain, (![B_88]: (~m2_orders_2(k1_xboole_0, '#skF_6', B_88) | ~v6_orders_2(k1_xboole_0, '#skF_6') | ~m1_orders_1(B_88, k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_160, c_219])).
% 2.53/1.37  tff(c_224, plain, (![B_88]: (~m2_orders_2(k1_xboole_0, '#skF_6', B_88) | ~m1_orders_1(B_88, k1_orders_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_164, c_221])).
% 2.53/1.37  tff(c_236, plain, (![B_92]: (~m2_orders_2(k1_xboole_0, '#skF_6', B_92) | ~m1_orders_1(B_92, k1_orders_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_224])).
% 2.53/1.37  tff(c_239, plain, (~m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_44, c_236])).
% 2.53/1.37  tff(c_243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150, c_239])).
% 2.53/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.37  
% 2.53/1.37  Inference rules
% 2.53/1.37  ----------------------
% 2.53/1.37  #Ref     : 0
% 2.53/1.37  #Sup     : 34
% 2.53/1.37  #Fact    : 0
% 2.53/1.37  #Define  : 0
% 2.53/1.37  #Split   : 1
% 2.53/1.37  #Chain   : 0
% 2.53/1.37  #Close   : 0
% 2.53/1.37  
% 2.53/1.37  Ordering : KBO
% 2.53/1.37  
% 2.53/1.37  Simplification rules
% 2.53/1.37  ----------------------
% 2.53/1.37  #Subsume      : 0
% 2.53/1.37  #Demod        : 68
% 2.53/1.37  #Tautology    : 15
% 2.53/1.37  #SimpNegUnit  : 13
% 2.53/1.37  #BackRed      : 2
% 2.53/1.37  
% 2.53/1.37  #Partial instantiations: 0
% 2.53/1.37  #Strategies tried      : 1
% 2.53/1.37  
% 2.53/1.37  Timing (in seconds)
% 2.53/1.37  ----------------------
% 2.53/1.38  Preprocessing        : 0.35
% 2.53/1.38  Parsing              : 0.18
% 2.53/1.38  CNF conversion       : 0.03
% 2.53/1.38  Main loop            : 0.22
% 2.53/1.38  Inferencing          : 0.08
% 2.53/1.38  Reduction            : 0.07
% 2.53/1.38  Demodulation         : 0.05
% 2.53/1.38  BG Simplification    : 0.02
% 2.53/1.38  Subsumption          : 0.03
% 2.53/1.38  Abstraction          : 0.01
% 2.53/1.38  MUC search           : 0.00
% 2.53/1.38  Cooper               : 0.00
% 2.53/1.38  Total                : 0.60
% 2.53/1.38  Index Insertion      : 0.00
% 2.53/1.38  Index Deletion       : 0.00
% 2.53/1.38  Index Matching       : 0.00
% 2.53/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
