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
% DateTime   : Thu Dec  3 10:19:44 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   64 (  81 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  152 ( 221 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_mcart_1 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k3_orders_2(A,k1_struct_0(A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_28,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_32,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_20,plain,(
    ! [A_30] :
      ( l1_struct_0(A_30)
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_43,plain,(
    ! [A_49] :
      ( k1_struct_0(A_49) = k1_xboole_0
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    ! [A_50] :
      ( k1_struct_0(A_50) = k1_xboole_0
      | ~ l1_orders_2(A_50) ) ),
    inference(resolution,[status(thm)],[c_20,c_43])).

tff(c_52,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_48])).

tff(c_28,plain,(
    k3_orders_2('#skF_2',k1_struct_0('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_53,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_28])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_38,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_36,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_34,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_85,plain,(
    ! [A_77,B_78,C_79] :
      ( m1_subset_1(k3_orders_2(A_77,B_78,C_79),k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_subset_1(C_79,u1_struct_0(A_77))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_orders_2(A_77)
      | ~ v5_orders_2(A_77)
      | ~ v4_orders_2(A_77)
      | ~ v3_orders_2(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_2,C_4,B_3] :
      ( m1_subset_1(A_2,C_4)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(C_4))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_115,plain,(
    ! [A_95,A_96,B_97,C_98] :
      ( m1_subset_1(A_95,u1_struct_0(A_96))
      | ~ r2_hidden(A_95,k3_orders_2(A_96,B_97,C_98))
      | ~ m1_subset_1(C_98,u1_struct_0(A_96))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_orders_2(A_96)
      | ~ v5_orders_2(A_96)
      | ~ v4_orders_2(A_96)
      | ~ v3_orders_2(A_96)
      | v2_struct_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_85,c_6])).

tff(c_119,plain,(
    ! [A_96,B_97,C_98] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_96,B_97,C_98)),u1_struct_0(A_96))
      | ~ m1_subset_1(C_98,u1_struct_0(A_96))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_orders_2(A_96)
      | ~ v5_orders_2(A_96)
      | ~ v4_orders_2(A_96)
      | ~ v3_orders_2(A_96)
      | v2_struct_0(A_96)
      | k3_orders_2(A_96,B_97,C_98) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_115])).

tff(c_97,plain,(
    ! [B_84,D_85,A_86,C_87] :
      ( r2_hidden(B_84,D_85)
      | ~ r2_hidden(B_84,k3_orders_2(A_86,D_85,C_87))
      | ~ m1_subset_1(D_85,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ m1_subset_1(C_87,u1_struct_0(A_86))
      | ~ m1_subset_1(B_84,u1_struct_0(A_86))
      | ~ l1_orders_2(A_86)
      | ~ v5_orders_2(A_86)
      | ~ v4_orders_2(A_86)
      | ~ v3_orders_2(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_132,plain,(
    ! [A_106,D_107,C_108] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_106,D_107,C_108)),D_107)
      | ~ m1_subset_1(D_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ m1_subset_1(C_108,u1_struct_0(A_106))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_106,D_107,C_108)),u1_struct_0(A_106))
      | ~ l1_orders_2(A_106)
      | ~ v5_orders_2(A_106)
      | ~ v4_orders_2(A_106)
      | ~ v3_orders_2(A_106)
      | v2_struct_0(A_106)
      | k3_orders_2(A_106,D_107,C_108) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_97])).

tff(c_136,plain,(
    ! [A_109,B_110,C_111] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_109,B_110,C_111)),B_110)
      | ~ m1_subset_1(C_111,u1_struct_0(A_109))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_orders_2(A_109)
      | ~ v5_orders_2(A_109)
      | ~ v4_orders_2(A_109)
      | ~ v3_orders_2(A_109)
      | v2_struct_0(A_109)
      | k3_orders_2(A_109,B_110,C_111) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_119,c_132])).

tff(c_59,plain,(
    ! [C_52,B_53,A_54] :
      ( ~ v1_xboole_0(C_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(C_52))
      | ~ r2_hidden(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_62,plain,(
    ! [A_1,A_54] :
      ( ~ v1_xboole_0(A_1)
      | ~ r2_hidden(A_54,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_59])).

tff(c_63,plain,(
    ! [A_54] : ~ r2_hidden(A_54,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_156,plain,(
    ! [C_111,A_109] :
      ( ~ m1_subset_1(C_111,u1_struct_0(A_109))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_orders_2(A_109)
      | ~ v5_orders_2(A_109)
      | ~ v4_orders_2(A_109)
      | ~ v3_orders_2(A_109)
      | v2_struct_0(A_109)
      | k3_orders_2(A_109,k1_xboole_0,C_111) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_136,c_63])).

tff(c_170,plain,(
    ! [C_115,A_116] :
      ( ~ m1_subset_1(C_115,u1_struct_0(A_116))
      | ~ l1_orders_2(A_116)
      | ~ v5_orders_2(A_116)
      | ~ v4_orders_2(A_116)
      | ~ v3_orders_2(A_116)
      | v2_struct_0(A_116)
      | k3_orders_2(A_116,k1_xboole_0,C_115) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_156])).

tff(c_176,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_170])).

tff(c_180,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_176])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_40,c_180])).

tff(c_183,plain,(
    ! [A_1] : ~ v1_xboole_0(A_1) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:46:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.28  
% 2.24/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.28  %$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_mcart_1 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.24/1.28  
% 2.24/1.28  %Foreground sorts:
% 2.24/1.28  
% 2.24/1.28  
% 2.24/1.28  %Background operators:
% 2.24/1.28  
% 2.24/1.28  
% 2.24/1.28  %Foreground operators:
% 2.24/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.24/1.28  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.24/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.24/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.28  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.24/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.28  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.24/1.28  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.24/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.24/1.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.24/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.28  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.24/1.28  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.24/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.24/1.28  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.24/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.24/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.28  
% 2.24/1.29  tff(f_125, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_orders_2)).
% 2.24/1.29  tff(f_82, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.24/1.29  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 2.24/1.29  tff(f_28, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.24/1.29  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 2.24/1.29  tff(f_78, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 2.24/1.29  tff(f_34, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.24/1.29  tff(f_108, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 2.24/1.29  tff(f_41, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.24/1.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.24/1.29  tff(c_32, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.24/1.29  tff(c_20, plain, (![A_30]: (l1_struct_0(A_30) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.24/1.29  tff(c_43, plain, (![A_49]: (k1_struct_0(A_49)=k1_xboole_0 | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.24/1.29  tff(c_48, plain, (![A_50]: (k1_struct_0(A_50)=k1_xboole_0 | ~l1_orders_2(A_50))), inference(resolution, [status(thm)], [c_20, c_43])).
% 2.24/1.29  tff(c_52, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_48])).
% 2.24/1.29  tff(c_28, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.24/1.29  tff(c_53, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_28])).
% 2.24/1.29  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.24/1.29  tff(c_38, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.24/1.29  tff(c_36, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.24/1.29  tff(c_34, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.24/1.29  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.24/1.29  tff(c_4, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.24/1.29  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.24/1.29  tff(c_85, plain, (![A_77, B_78, C_79]: (m1_subset_1(k3_orders_2(A_77, B_78, C_79), k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_subset_1(C_79, u1_struct_0(A_77)) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_orders_2(A_77) | ~v5_orders_2(A_77) | ~v4_orders_2(A_77) | ~v3_orders_2(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.24/1.29  tff(c_6, plain, (![A_2, C_4, B_3]: (m1_subset_1(A_2, C_4) | ~m1_subset_1(B_3, k1_zfmisc_1(C_4)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.24/1.29  tff(c_115, plain, (![A_95, A_96, B_97, C_98]: (m1_subset_1(A_95, u1_struct_0(A_96)) | ~r2_hidden(A_95, k3_orders_2(A_96, B_97, C_98)) | ~m1_subset_1(C_98, u1_struct_0(A_96)) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_orders_2(A_96) | ~v5_orders_2(A_96) | ~v4_orders_2(A_96) | ~v3_orders_2(A_96) | v2_struct_0(A_96))), inference(resolution, [status(thm)], [c_85, c_6])).
% 2.24/1.29  tff(c_119, plain, (![A_96, B_97, C_98]: (m1_subset_1('#skF_1'(k3_orders_2(A_96, B_97, C_98)), u1_struct_0(A_96)) | ~m1_subset_1(C_98, u1_struct_0(A_96)) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_orders_2(A_96) | ~v5_orders_2(A_96) | ~v4_orders_2(A_96) | ~v3_orders_2(A_96) | v2_struct_0(A_96) | k3_orders_2(A_96, B_97, C_98)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_115])).
% 2.24/1.29  tff(c_97, plain, (![B_84, D_85, A_86, C_87]: (r2_hidden(B_84, D_85) | ~r2_hidden(B_84, k3_orders_2(A_86, D_85, C_87)) | ~m1_subset_1(D_85, k1_zfmisc_1(u1_struct_0(A_86))) | ~m1_subset_1(C_87, u1_struct_0(A_86)) | ~m1_subset_1(B_84, u1_struct_0(A_86)) | ~l1_orders_2(A_86) | ~v5_orders_2(A_86) | ~v4_orders_2(A_86) | ~v3_orders_2(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.24/1.29  tff(c_132, plain, (![A_106, D_107, C_108]: (r2_hidden('#skF_1'(k3_orders_2(A_106, D_107, C_108)), D_107) | ~m1_subset_1(D_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~m1_subset_1(C_108, u1_struct_0(A_106)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_106, D_107, C_108)), u1_struct_0(A_106)) | ~l1_orders_2(A_106) | ~v5_orders_2(A_106) | ~v4_orders_2(A_106) | ~v3_orders_2(A_106) | v2_struct_0(A_106) | k3_orders_2(A_106, D_107, C_108)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_97])).
% 2.24/1.29  tff(c_136, plain, (![A_109, B_110, C_111]: (r2_hidden('#skF_1'(k3_orders_2(A_109, B_110, C_111)), B_110) | ~m1_subset_1(C_111, u1_struct_0(A_109)) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_orders_2(A_109) | ~v5_orders_2(A_109) | ~v4_orders_2(A_109) | ~v3_orders_2(A_109) | v2_struct_0(A_109) | k3_orders_2(A_109, B_110, C_111)=k1_xboole_0)), inference(resolution, [status(thm)], [c_119, c_132])).
% 2.24/1.29  tff(c_59, plain, (![C_52, B_53, A_54]: (~v1_xboole_0(C_52) | ~m1_subset_1(B_53, k1_zfmisc_1(C_52)) | ~r2_hidden(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.24/1.29  tff(c_62, plain, (![A_1, A_54]: (~v1_xboole_0(A_1) | ~r2_hidden(A_54, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_59])).
% 2.24/1.29  tff(c_63, plain, (![A_54]: (~r2_hidden(A_54, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_62])).
% 2.24/1.29  tff(c_156, plain, (![C_111, A_109]: (~m1_subset_1(C_111, u1_struct_0(A_109)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_orders_2(A_109) | ~v5_orders_2(A_109) | ~v4_orders_2(A_109) | ~v3_orders_2(A_109) | v2_struct_0(A_109) | k3_orders_2(A_109, k1_xboole_0, C_111)=k1_xboole_0)), inference(resolution, [status(thm)], [c_136, c_63])).
% 2.24/1.29  tff(c_170, plain, (![C_115, A_116]: (~m1_subset_1(C_115, u1_struct_0(A_116)) | ~l1_orders_2(A_116) | ~v5_orders_2(A_116) | ~v4_orders_2(A_116) | ~v3_orders_2(A_116) | v2_struct_0(A_116) | k3_orders_2(A_116, k1_xboole_0, C_115)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_156])).
% 2.24/1.29  tff(c_176, plain, (~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_170])).
% 2.24/1.29  tff(c_180, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_176])).
% 2.24/1.29  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_40, c_180])).
% 2.24/1.29  tff(c_183, plain, (![A_1]: (~v1_xboole_0(A_1))), inference(splitRight, [status(thm)], [c_62])).
% 2.24/1.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.24/1.29  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_2])).
% 2.24/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.29  
% 2.24/1.29  Inference rules
% 2.24/1.29  ----------------------
% 2.24/1.29  #Ref     : 0
% 2.24/1.29  #Sup     : 30
% 2.24/1.29  #Fact    : 0
% 2.24/1.29  #Define  : 0
% 2.24/1.29  #Split   : 2
% 2.24/1.29  #Chain   : 0
% 2.24/1.29  #Close   : 0
% 2.24/1.29  
% 2.24/1.29  Ordering : KBO
% 2.24/1.29  
% 2.24/1.29  Simplification rules
% 2.24/1.29  ----------------------
% 2.24/1.29  #Subsume      : 5
% 2.24/1.29  #Demod        : 10
% 2.24/1.30  #Tautology    : 3
% 2.24/1.30  #SimpNegUnit  : 3
% 2.24/1.30  #BackRed      : 2
% 2.24/1.30  
% 2.24/1.30  #Partial instantiations: 0
% 2.24/1.30  #Strategies tried      : 1
% 2.24/1.30  
% 2.24/1.30  Timing (in seconds)
% 2.24/1.30  ----------------------
% 2.24/1.30  Preprocessing        : 0.31
% 2.24/1.30  Parsing              : 0.18
% 2.24/1.30  CNF conversion       : 0.02
% 2.24/1.30  Main loop            : 0.24
% 2.24/1.30  Inferencing          : 0.09
% 2.24/1.30  Reduction            : 0.06
% 2.24/1.30  Demodulation         : 0.04
% 2.24/1.30  BG Simplification    : 0.01
% 2.24/1.30  Subsumption          : 0.05
% 2.24/1.30  Abstraction          : 0.01
% 2.24/1.30  MUC search           : 0.00
% 2.24/1.30  Cooper               : 0.00
% 2.24/1.30  Total                : 0.58
% 2.24/1.30  Index Insertion      : 0.00
% 2.24/1.30  Index Deletion       : 0.00
% 2.24/1.30  Index Matching       : 0.00
% 2.24/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
