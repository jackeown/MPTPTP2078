%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:46 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   60 (  70 expanded)
%              Number of leaves         :   31 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  151 ( 205 expanded)
%              Number of equality atoms :   17 (  26 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k3_orders_2(A,k1_struct_0(A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_orders_2)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_99,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_28,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_16,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    ! [A_34] :
      ( k1_struct_0(A_34) = k1_xboole_0
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_45,plain,(
    ! [A_35] :
      ( k1_struct_0(A_35) = k1_xboole_0
      | ~ l1_orders_2(A_35) ) ),
    inference(resolution,[status(thm)],[c_16,c_40])).

tff(c_49,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_45])).

tff(c_24,plain,(
    k3_orders_2('#skF_2',k1_struct_0('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_50,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_24])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_34,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_32,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_30,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    ! [A_45,B_46,C_47] :
      ( m1_subset_1(k3_orders_2(A_45,B_46,C_47),k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_subset_1(C_47,u1_struct_0(A_45))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_orders_2(A_45)
      | ~ v5_orders_2(A_45)
      | ~ v4_orders_2(A_45)
      | ~ v3_orders_2(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_5,C_7,B_6] :
      ( m1_subset_1(A_5,C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_82,plain,(
    ! [A_48,A_49,B_50,C_51] :
      ( m1_subset_1(A_48,u1_struct_0(A_49))
      | ~ r2_hidden(A_48,k3_orders_2(A_49,B_50,C_51))
      | ~ m1_subset_1(C_51,u1_struct_0(A_49))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_orders_2(A_49)
      | ~ v5_orders_2(A_49)
      | ~ v4_orders_2(A_49)
      | ~ v3_orders_2(A_49)
      | v2_struct_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_78,c_8])).

tff(c_86,plain,(
    ! [A_49,B_50,C_51] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_49,B_50,C_51)),u1_struct_0(A_49))
      | ~ m1_subset_1(C_51,u1_struct_0(A_49))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_orders_2(A_49)
      | ~ v5_orders_2(A_49)
      | ~ v4_orders_2(A_49)
      | ~ v3_orders_2(A_49)
      | v2_struct_0(A_49)
      | k3_orders_2(A_49,B_50,C_51) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_82])).

tff(c_87,plain,(
    ! [B_52,D_53,A_54,C_55] :
      ( r2_hidden(B_52,D_53)
      | ~ r2_hidden(B_52,k3_orders_2(A_54,D_53,C_55))
      | ~ m1_subset_1(D_53,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(C_55,u1_struct_0(A_54))
      | ~ m1_subset_1(B_52,u1_struct_0(A_54))
      | ~ l1_orders_2(A_54)
      | ~ v5_orders_2(A_54)
      | ~ v4_orders_2(A_54)
      | ~ v3_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_127,plain,(
    ! [A_73,D_74,C_75] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_73,D_74,C_75)),D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(C_75,u1_struct_0(A_73))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_73,D_74,C_75)),u1_struct_0(A_73))
      | ~ l1_orders_2(A_73)
      | ~ v5_orders_2(A_73)
      | ~ v4_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73)
      | k3_orders_2(A_73,D_74,C_75) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_87])).

tff(c_131,plain,(
    ! [A_76,B_77,C_78] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_76,B_77,C_78)),B_77)
      | ~ m1_subset_1(C_78,u1_struct_0(A_76))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_orders_2(A_76)
      | ~ v5_orders_2(A_76)
      | ~ v4_orders_2(A_76)
      | ~ v3_orders_2(A_76)
      | v2_struct_0(A_76)
      | k3_orders_2(A_76,B_77,C_78) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_86,c_127])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( ~ r1_tarski(B_9,A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_154,plain,(
    ! [B_79,A_80,C_81] :
      ( ~ r1_tarski(B_79,'#skF_1'(k3_orders_2(A_80,B_79,C_81)))
      | ~ m1_subset_1(C_81,u1_struct_0(A_80))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_orders_2(A_80)
      | ~ v5_orders_2(A_80)
      | ~ v4_orders_2(A_80)
      | ~ v3_orders_2(A_80)
      | v2_struct_0(A_80)
      | k3_orders_2(A_80,B_79,C_81) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_131,c_10])).

tff(c_158,plain,(
    ! [C_81,A_80] :
      ( ~ m1_subset_1(C_81,u1_struct_0(A_80))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_orders_2(A_80)
      | ~ v5_orders_2(A_80)
      | ~ v4_orders_2(A_80)
      | ~ v3_orders_2(A_80)
      | v2_struct_0(A_80)
      | k3_orders_2(A_80,k1_xboole_0,C_81) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_154])).

tff(c_162,plain,(
    ! [C_82,A_83] :
      ( ~ m1_subset_1(C_82,u1_struct_0(A_83))
      | ~ l1_orders_2(A_83)
      | ~ v5_orders_2(A_83)
      | ~ v4_orders_2(A_83)
      | ~ v3_orders_2(A_83)
      | v2_struct_0(A_83)
      | k3_orders_2(A_83,k1_xboole_0,C_82) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_158])).

tff(c_168,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_162])).

tff(c_172,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_168])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_36,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:27:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.35  
% 2.27/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.36  %$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.27/1.36  
% 2.27/1.36  %Foreground sorts:
% 2.27/1.36  
% 2.27/1.36  
% 2.27/1.36  %Background operators:
% 2.27/1.36  
% 2.27/1.36  
% 2.27/1.36  %Foreground operators:
% 2.27/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.27/1.36  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.27/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.27/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.36  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.27/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.36  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.27/1.36  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.27/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.27/1.36  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.27/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.36  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.27/1.36  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.27/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.27/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.36  
% 2.54/1.37  tff(f_116, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_orders_2)).
% 2.54/1.37  tff(f_73, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.54/1.37  tff(f_52, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 2.54/1.37  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.54/1.37  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.54/1.37  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.54/1.37  tff(f_69, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 2.54/1.37  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.54/1.37  tff(f_99, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 2.54/1.37  tff(f_48, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.54/1.37  tff(c_28, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.54/1.37  tff(c_16, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.54/1.37  tff(c_40, plain, (![A_34]: (k1_struct_0(A_34)=k1_xboole_0 | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.54/1.37  tff(c_45, plain, (![A_35]: (k1_struct_0(A_35)=k1_xboole_0 | ~l1_orders_2(A_35))), inference(resolution, [status(thm)], [c_16, c_40])).
% 2.54/1.37  tff(c_49, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_45])).
% 2.54/1.37  tff(c_24, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.54/1.37  tff(c_50, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_49, c_24])).
% 2.54/1.37  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.54/1.37  tff(c_34, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.54/1.37  tff(c_32, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.54/1.37  tff(c_30, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.54/1.37  tff(c_26, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.54/1.37  tff(c_6, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.54/1.37  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.37  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.54/1.37  tff(c_78, plain, (![A_45, B_46, C_47]: (m1_subset_1(k3_orders_2(A_45, B_46, C_47), k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_subset_1(C_47, u1_struct_0(A_45)) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_orders_2(A_45) | ~v5_orders_2(A_45) | ~v4_orders_2(A_45) | ~v3_orders_2(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.54/1.37  tff(c_8, plain, (![A_5, C_7, B_6]: (m1_subset_1(A_5, C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.54/1.37  tff(c_82, plain, (![A_48, A_49, B_50, C_51]: (m1_subset_1(A_48, u1_struct_0(A_49)) | ~r2_hidden(A_48, k3_orders_2(A_49, B_50, C_51)) | ~m1_subset_1(C_51, u1_struct_0(A_49)) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_orders_2(A_49) | ~v5_orders_2(A_49) | ~v4_orders_2(A_49) | ~v3_orders_2(A_49) | v2_struct_0(A_49))), inference(resolution, [status(thm)], [c_78, c_8])).
% 2.54/1.37  tff(c_86, plain, (![A_49, B_50, C_51]: (m1_subset_1('#skF_1'(k3_orders_2(A_49, B_50, C_51)), u1_struct_0(A_49)) | ~m1_subset_1(C_51, u1_struct_0(A_49)) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_orders_2(A_49) | ~v5_orders_2(A_49) | ~v4_orders_2(A_49) | ~v3_orders_2(A_49) | v2_struct_0(A_49) | k3_orders_2(A_49, B_50, C_51)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_82])).
% 2.54/1.37  tff(c_87, plain, (![B_52, D_53, A_54, C_55]: (r2_hidden(B_52, D_53) | ~r2_hidden(B_52, k3_orders_2(A_54, D_53, C_55)) | ~m1_subset_1(D_53, k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_subset_1(C_55, u1_struct_0(A_54)) | ~m1_subset_1(B_52, u1_struct_0(A_54)) | ~l1_orders_2(A_54) | ~v5_orders_2(A_54) | ~v4_orders_2(A_54) | ~v3_orders_2(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.54/1.37  tff(c_127, plain, (![A_73, D_74, C_75]: (r2_hidden('#skF_1'(k3_orders_2(A_73, D_74, C_75)), D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(C_75, u1_struct_0(A_73)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_73, D_74, C_75)), u1_struct_0(A_73)) | ~l1_orders_2(A_73) | ~v5_orders_2(A_73) | ~v4_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73) | k3_orders_2(A_73, D_74, C_75)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_87])).
% 2.54/1.37  tff(c_131, plain, (![A_76, B_77, C_78]: (r2_hidden('#skF_1'(k3_orders_2(A_76, B_77, C_78)), B_77) | ~m1_subset_1(C_78, u1_struct_0(A_76)) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_orders_2(A_76) | ~v5_orders_2(A_76) | ~v4_orders_2(A_76) | ~v3_orders_2(A_76) | v2_struct_0(A_76) | k3_orders_2(A_76, B_77, C_78)=k1_xboole_0)), inference(resolution, [status(thm)], [c_86, c_127])).
% 2.54/1.37  tff(c_10, plain, (![B_9, A_8]: (~r1_tarski(B_9, A_8) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.54/1.37  tff(c_154, plain, (![B_79, A_80, C_81]: (~r1_tarski(B_79, '#skF_1'(k3_orders_2(A_80, B_79, C_81))) | ~m1_subset_1(C_81, u1_struct_0(A_80)) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_orders_2(A_80) | ~v5_orders_2(A_80) | ~v4_orders_2(A_80) | ~v3_orders_2(A_80) | v2_struct_0(A_80) | k3_orders_2(A_80, B_79, C_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_131, c_10])).
% 2.54/1.37  tff(c_158, plain, (![C_81, A_80]: (~m1_subset_1(C_81, u1_struct_0(A_80)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_orders_2(A_80) | ~v5_orders_2(A_80) | ~v4_orders_2(A_80) | ~v3_orders_2(A_80) | v2_struct_0(A_80) | k3_orders_2(A_80, k1_xboole_0, C_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_154])).
% 2.54/1.37  tff(c_162, plain, (![C_82, A_83]: (~m1_subset_1(C_82, u1_struct_0(A_83)) | ~l1_orders_2(A_83) | ~v5_orders_2(A_83) | ~v4_orders_2(A_83) | ~v3_orders_2(A_83) | v2_struct_0(A_83) | k3_orders_2(A_83, k1_xboole_0, C_82)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_158])).
% 2.54/1.37  tff(c_168, plain, (~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_162])).
% 2.54/1.37  tff(c_172, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_168])).
% 2.54/1.37  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_36, c_172])).
% 2.54/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.37  
% 2.54/1.37  Inference rules
% 2.54/1.37  ----------------------
% 2.54/1.37  #Ref     : 0
% 2.54/1.37  #Sup     : 27
% 2.54/1.37  #Fact    : 0
% 2.54/1.37  #Define  : 0
% 2.54/1.37  #Split   : 0
% 2.54/1.37  #Chain   : 0
% 2.54/1.37  #Close   : 0
% 2.54/1.37  
% 2.54/1.37  Ordering : KBO
% 2.54/1.37  
% 2.54/1.37  Simplification rules
% 2.54/1.37  ----------------------
% 2.54/1.37  #Subsume      : 2
% 2.54/1.37  #Demod        : 10
% 2.54/1.37  #Tautology    : 6
% 2.54/1.37  #SimpNegUnit  : 1
% 2.54/1.37  #BackRed      : 1
% 2.54/1.37  
% 2.54/1.37  #Partial instantiations: 0
% 2.54/1.37  #Strategies tried      : 1
% 2.54/1.37  
% 2.54/1.37  Timing (in seconds)
% 2.54/1.37  ----------------------
% 2.54/1.38  Preprocessing        : 0.32
% 2.54/1.38  Parsing              : 0.18
% 2.54/1.38  CNF conversion       : 0.03
% 2.54/1.38  Main loop            : 0.22
% 2.54/1.38  Inferencing          : 0.10
% 2.54/1.38  Reduction            : 0.05
% 2.54/1.38  Demodulation         : 0.04
% 2.54/1.38  BG Simplification    : 0.01
% 2.54/1.38  Subsumption          : 0.05
% 2.54/1.38  Abstraction          : 0.01
% 2.54/1.38  MUC search           : 0.00
% 2.54/1.38  Cooper               : 0.00
% 2.54/1.38  Total                : 0.58
% 2.54/1.38  Index Insertion      : 0.00
% 2.54/1.38  Index Deletion       : 0.00
% 2.54/1.38  Index Matching       : 0.00
% 2.54/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
