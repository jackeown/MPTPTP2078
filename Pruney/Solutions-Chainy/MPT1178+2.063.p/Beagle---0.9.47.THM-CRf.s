%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:10 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 126 expanded)
%              Number of leaves         :   35 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  133 ( 339 expanded)
%              Number of equality atoms :   20 (  70 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
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

tff(f_126,axiom,(
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

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_71,axiom,(
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

tff(f_106,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_44,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_42,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_40,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_38,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_36,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_34,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [A_50,B_51] :
      ( k3_tarski(A_50) != k1_xboole_0
      | ~ r2_hidden(B_51,A_50)
      | k1_xboole_0 = B_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_80,plain,(
    ! [A_52] :
      ( k3_tarski(A_52) != k1_xboole_0
      | '#skF_1'(A_52) = k1_xboole_0
      | k1_xboole_0 = A_52 ) ),
    inference(resolution,[status(thm)],[c_4,c_71])).

tff(c_88,plain,
    ( '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0
    | k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_80])).

tff(c_124,plain,(
    k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_135,plain,(
    ! [A_61,B_62] :
      ( ~ v1_xboole_0(k4_orders_2(A_61,B_62))
      | ~ m1_orders_1(B_62,k1_orders_1(u1_struct_0(A_61)))
      | ~ l1_orders_2(A_61)
      | ~ v5_orders_2(A_61)
      | ~ v4_orders_2(A_61)
      | ~ v3_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_138,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_135])).

tff(c_141,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_2,c_124,c_138])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_141])).

tff(c_145,plain,(
    k4_orders_2('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_144,plain,(
    '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_149,plain,
    ( r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6'))
    | k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_4])).

tff(c_152,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_149])).

tff(c_188,plain,(
    ! [D_73,A_74,B_75] :
      ( m2_orders_2(D_73,A_74,B_75)
      | ~ r2_hidden(D_73,k4_orders_2(A_74,B_75))
      | ~ m1_orders_1(B_75,k1_orders_1(u1_struct_0(A_74)))
      | ~ l1_orders_2(A_74)
      | ~ v5_orders_2(A_74)
      | ~ v4_orders_2(A_74)
      | ~ v3_orders_2(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_192,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_152,c_188])).

tff(c_205,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_192])).

tff(c_206,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_205])).

tff(c_214,plain,(
    ! [B_76,A_77,C_78] :
      ( r2_hidden(k1_funct_1(B_76,u1_struct_0(A_77)),C_78)
      | ~ m2_orders_2(C_78,A_77,B_76)
      | ~ m1_orders_1(B_76,k1_orders_1(u1_struct_0(A_77)))
      | ~ l1_orders_2(A_77)
      | ~ v5_orders_2(A_77)
      | ~ v4_orders_2(A_77)
      | ~ v3_orders_2(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_90,plain,(
    ! [C_54,B_55,A_56] :
      ( ~ v1_xboole_0(C_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(C_54))
      | ~ r2_hidden(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_93,plain,(
    ! [A_3,A_56] :
      ( ~ v1_xboole_0(A_3)
      | ~ r2_hidden(A_56,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_94,plain,(
    ! [A_56] : ~ r2_hidden(A_56,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_233,plain,(
    ! [A_82,B_83] :
      ( ~ m2_orders_2(k1_xboole_0,A_82,B_83)
      | ~ m1_orders_1(B_83,k1_orders_1(u1_struct_0(A_82)))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82)
      | ~ v4_orders_2(A_82)
      | ~ v3_orders_2(A_82)
      | v2_struct_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_214,c_94])).

tff(c_236,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_233])).

tff(c_239,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_206,c_236])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_239])).

tff(c_242,plain,(
    ! [A_3] : ~ v1_xboole_0(A_3) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:13:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.30  
% 2.45/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.31  %$ m2_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.45/1.31  
% 2.45/1.31  %Foreground sorts:
% 2.45/1.31  
% 2.45/1.31  
% 2.45/1.31  %Background operators:
% 2.45/1.31  
% 2.45/1.31  
% 2.45/1.31  %Foreground operators:
% 2.45/1.31  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.45/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.45/1.31  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.45/1.31  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.45/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.45/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.31  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.45/1.31  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.45/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.45/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.45/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.45/1.31  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.45/1.31  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.45/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.45/1.31  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.45/1.31  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.45/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.45/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.45/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.45/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.45/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.31  
% 2.45/1.32  tff(f_144, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.45/1.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.45/1.32  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.45/1.32  tff(f_126, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 2.45/1.32  tff(f_87, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.45/1.32  tff(f_71, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.45/1.32  tff(f_106, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 2.45/1.32  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.45/1.32  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.45/1.32  tff(c_46, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.45/1.32  tff(c_44, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.45/1.32  tff(c_42, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.45/1.32  tff(c_40, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.45/1.32  tff(c_38, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.45/1.32  tff(c_36, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.45/1.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.45/1.32  tff(c_34, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.45/1.32  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.45/1.32  tff(c_71, plain, (![A_50, B_51]: (k3_tarski(A_50)!=k1_xboole_0 | ~r2_hidden(B_51, A_50) | k1_xboole_0=B_51)), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.45/1.32  tff(c_80, plain, (![A_52]: (k3_tarski(A_52)!=k1_xboole_0 | '#skF_1'(A_52)=k1_xboole_0 | k1_xboole_0=A_52)), inference(resolution, [status(thm)], [c_4, c_71])).
% 2.45/1.32  tff(c_88, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0 | k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_34, c_80])).
% 2.45/1.32  tff(c_124, plain, (k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_88])).
% 2.45/1.32  tff(c_135, plain, (![A_61, B_62]: (~v1_xboole_0(k4_orders_2(A_61, B_62)) | ~m1_orders_1(B_62, k1_orders_1(u1_struct_0(A_61))) | ~l1_orders_2(A_61) | ~v5_orders_2(A_61) | ~v4_orders_2(A_61) | ~v3_orders_2(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.45/1.32  tff(c_138, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_135])).
% 2.45/1.32  tff(c_141, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_2, c_124, c_138])).
% 2.45/1.32  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_141])).
% 2.45/1.32  tff(c_145, plain, (k4_orders_2('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_88])).
% 2.45/1.32  tff(c_144, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_88])).
% 2.45/1.32  tff(c_149, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6')) | k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_144, c_4])).
% 2.45/1.32  tff(c_152, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_145, c_149])).
% 2.45/1.32  tff(c_188, plain, (![D_73, A_74, B_75]: (m2_orders_2(D_73, A_74, B_75) | ~r2_hidden(D_73, k4_orders_2(A_74, B_75)) | ~m1_orders_1(B_75, k1_orders_1(u1_struct_0(A_74))) | ~l1_orders_2(A_74) | ~v5_orders_2(A_74) | ~v4_orders_2(A_74) | ~v3_orders_2(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.45/1.32  tff(c_192, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_152, c_188])).
% 2.45/1.32  tff(c_205, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_192])).
% 2.45/1.32  tff(c_206, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_46, c_205])).
% 2.45/1.32  tff(c_214, plain, (![B_76, A_77, C_78]: (r2_hidden(k1_funct_1(B_76, u1_struct_0(A_77)), C_78) | ~m2_orders_2(C_78, A_77, B_76) | ~m1_orders_1(B_76, k1_orders_1(u1_struct_0(A_77))) | ~l1_orders_2(A_77) | ~v5_orders_2(A_77) | ~v4_orders_2(A_77) | ~v3_orders_2(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.45/1.32  tff(c_6, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.45/1.32  tff(c_90, plain, (![C_54, B_55, A_56]: (~v1_xboole_0(C_54) | ~m1_subset_1(B_55, k1_zfmisc_1(C_54)) | ~r2_hidden(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.45/1.32  tff(c_93, plain, (![A_3, A_56]: (~v1_xboole_0(A_3) | ~r2_hidden(A_56, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_90])).
% 2.45/1.32  tff(c_94, plain, (![A_56]: (~r2_hidden(A_56, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_93])).
% 2.45/1.32  tff(c_233, plain, (![A_82, B_83]: (~m2_orders_2(k1_xboole_0, A_82, B_83) | ~m1_orders_1(B_83, k1_orders_1(u1_struct_0(A_82))) | ~l1_orders_2(A_82) | ~v5_orders_2(A_82) | ~v4_orders_2(A_82) | ~v3_orders_2(A_82) | v2_struct_0(A_82))), inference(resolution, [status(thm)], [c_214, c_94])).
% 2.45/1.32  tff(c_236, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_233])).
% 2.45/1.32  tff(c_239, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_206, c_236])).
% 2.45/1.32  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_239])).
% 2.45/1.32  tff(c_242, plain, (![A_3]: (~v1_xboole_0(A_3))), inference(splitRight, [status(thm)], [c_93])).
% 2.45/1.32  tff(c_244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_242, c_2])).
% 2.45/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.32  
% 2.45/1.32  Inference rules
% 2.45/1.32  ----------------------
% 2.45/1.32  #Ref     : 0
% 2.45/1.32  #Sup     : 40
% 2.45/1.32  #Fact    : 0
% 2.45/1.32  #Define  : 0
% 2.45/1.32  #Split   : 2
% 2.45/1.32  #Chain   : 0
% 2.45/1.32  #Close   : 0
% 2.45/1.32  
% 2.45/1.32  Ordering : KBO
% 2.45/1.32  
% 2.45/1.32  Simplification rules
% 2.45/1.32  ----------------------
% 2.45/1.32  #Subsume      : 3
% 2.45/1.32  #Demod        : 33
% 2.45/1.32  #Tautology    : 21
% 2.45/1.32  #SimpNegUnit  : 8
% 2.45/1.32  #BackRed      : 2
% 2.45/1.32  
% 2.45/1.32  #Partial instantiations: 0
% 2.45/1.32  #Strategies tried      : 1
% 2.45/1.32  
% 2.45/1.32  Timing (in seconds)
% 2.45/1.32  ----------------------
% 2.45/1.33  Preprocessing        : 0.33
% 2.45/1.33  Parsing              : 0.18
% 2.45/1.33  CNF conversion       : 0.03
% 2.45/1.33  Main loop            : 0.22
% 2.45/1.33  Inferencing          : 0.09
% 2.45/1.33  Reduction            : 0.06
% 2.45/1.33  Demodulation         : 0.05
% 2.45/1.33  BG Simplification    : 0.02
% 2.45/1.33  Subsumption          : 0.03
% 2.45/1.33  Abstraction          : 0.01
% 2.45/1.33  MUC search           : 0.00
% 2.45/1.33  Cooper               : 0.00
% 2.45/1.33  Total                : 0.58
% 2.45/1.33  Index Insertion      : 0.00
% 2.45/1.33  Index Deletion       : 0.00
% 2.45/1.33  Index Matching       : 0.00
% 2.45/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
