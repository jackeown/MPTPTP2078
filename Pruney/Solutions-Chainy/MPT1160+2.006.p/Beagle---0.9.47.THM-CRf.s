%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:44 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   66 (  86 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  180 ( 259 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
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

tff(f_78,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_74,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_104,axiom,(
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

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_30,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_18,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_41,plain,(
    ! [A_34] :
      ( k1_struct_0(A_34) = k1_xboole_0
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_46,plain,(
    ! [A_35] :
      ( k1_struct_0(A_35) = k1_xboole_0
      | ~ l1_orders_2(A_35) ) ),
    inference(resolution,[status(thm)],[c_18,c_41])).

tff(c_50,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_46])).

tff(c_26,plain,(
    k3_orders_2('#skF_2',k1_struct_0('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_51,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_26])).

tff(c_36,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_34,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_32,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_8,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] :
      ( m1_subset_1(k3_orders_2(A_12,B_13,C_14),k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_subset_1(C_14,u1_struct_0(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_orders_2(A_12)
      | ~ v5_orders_2(A_12)
      | ~ v4_orders_2(A_12)
      | ~ v3_orders_2(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_114,plain,(
    ! [A_58,B_59,C_60] :
      ( m1_subset_1(k3_orders_2(A_58,B_59,C_60),k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_subset_1(C_60,u1_struct_0(A_58))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_orders_2(A_58)
      | ~ v5_orders_2(A_58)
      | ~ v4_orders_2(A_58)
      | ~ v3_orders_2(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( m1_subset_1(A_5,C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_183,plain,(
    ! [A_74,A_75,B_76,C_77] :
      ( m1_subset_1(A_74,u1_struct_0(A_75))
      | ~ r2_hidden(A_74,k3_orders_2(A_75,B_76,C_77))
      | ~ m1_subset_1(C_77,u1_struct_0(A_75))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_orders_2(A_75)
      | ~ v5_orders_2(A_75)
      | ~ v4_orders_2(A_75)
      | ~ v3_orders_2(A_75)
      | v2_struct_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_114,c_10])).

tff(c_187,plain,(
    ! [A_1,A_75,B_76,C_77] :
      ( m1_subset_1('#skF_1'(A_1,k3_orders_2(A_75,B_76,C_77)),u1_struct_0(A_75))
      | ~ m1_subset_1(C_77,u1_struct_0(A_75))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_orders_2(A_75)
      | ~ v5_orders_2(A_75)
      | ~ v4_orders_2(A_75)
      | ~ v3_orders_2(A_75)
      | v2_struct_0(A_75)
      | k3_orders_2(A_75,B_76,C_77) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_75,B_76,C_77),k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_4,c_183])).

tff(c_178,plain,(
    ! [B_70,D_71,A_72,C_73] :
      ( r2_hidden(B_70,D_71)
      | ~ r2_hidden(B_70,k3_orders_2(A_72,D_71,C_73))
      | ~ m1_subset_1(D_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ m1_subset_1(C_73,u1_struct_0(A_72))
      | ~ m1_subset_1(B_70,u1_struct_0(A_72))
      | ~ l1_orders_2(A_72)
      | ~ v5_orders_2(A_72)
      | ~ v4_orders_2(A_72)
      | ~ v3_orders_2(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_515,plain,(
    ! [A_143,A_144,D_145,C_146] :
      ( r2_hidden('#skF_1'(A_143,k3_orders_2(A_144,D_145,C_146)),D_145)
      | ~ m1_subset_1(D_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ m1_subset_1(C_146,u1_struct_0(A_144))
      | ~ m1_subset_1('#skF_1'(A_143,k3_orders_2(A_144,D_145,C_146)),u1_struct_0(A_144))
      | ~ l1_orders_2(A_144)
      | ~ v5_orders_2(A_144)
      | ~ v4_orders_2(A_144)
      | ~ v3_orders_2(A_144)
      | v2_struct_0(A_144)
      | k3_orders_2(A_144,D_145,C_146) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_144,D_145,C_146),k1_zfmisc_1(A_143)) ) ),
    inference(resolution,[status(thm)],[c_4,c_178])).

tff(c_527,plain,(
    ! [A_147,A_148,B_149,C_150] :
      ( r2_hidden('#skF_1'(A_147,k3_orders_2(A_148,B_149,C_150)),B_149)
      | ~ m1_subset_1(C_150,u1_struct_0(A_148))
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_orders_2(A_148)
      | ~ v5_orders_2(A_148)
      | ~ v4_orders_2(A_148)
      | ~ v3_orders_2(A_148)
      | v2_struct_0(A_148)
      | k3_orders_2(A_148,B_149,C_150) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_148,B_149,C_150),k1_zfmisc_1(A_147)) ) ),
    inference(resolution,[status(thm)],[c_187,c_515])).

tff(c_56,plain,(
    ! [C_36,B_37,A_38] :
      ( ~ v1_xboole_0(C_36)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(C_36))
      | ~ r2_hidden(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_59,plain,(
    ! [A_4,A_38] :
      ( ~ v1_xboole_0(A_4)
      | ~ r2_hidden(A_38,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_56])).

tff(c_64,plain,(
    ! [A_38] : ~ r2_hidden(A_38,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_559,plain,(
    ! [C_150,A_148,A_147] :
      ( ~ m1_subset_1(C_150,u1_struct_0(A_148))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_orders_2(A_148)
      | ~ v5_orders_2(A_148)
      | ~ v4_orders_2(A_148)
      | ~ v3_orders_2(A_148)
      | v2_struct_0(A_148)
      | k3_orders_2(A_148,k1_xboole_0,C_150) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_148,k1_xboole_0,C_150),k1_zfmisc_1(A_147)) ) ),
    inference(resolution,[status(thm)],[c_527,c_64])).

tff(c_589,plain,(
    ! [C_155,A_156,A_157] :
      ( ~ m1_subset_1(C_155,u1_struct_0(A_156))
      | ~ l1_orders_2(A_156)
      | ~ v5_orders_2(A_156)
      | ~ v4_orders_2(A_156)
      | ~ v3_orders_2(A_156)
      | v2_struct_0(A_156)
      | k3_orders_2(A_156,k1_xboole_0,C_155) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_156,k1_xboole_0,C_155),k1_zfmisc_1(A_157)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_559])).

tff(c_593,plain,(
    ! [A_12,C_14] :
      ( k3_orders_2(A_12,k1_xboole_0,C_14) = k1_xboole_0
      | ~ m1_subset_1(C_14,u1_struct_0(A_12))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_orders_2(A_12)
      | ~ v5_orders_2(A_12)
      | ~ v4_orders_2(A_12)
      | ~ v3_orders_2(A_12)
      | v2_struct_0(A_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_589])).

tff(c_597,plain,(
    ! [A_158,C_159] :
      ( k3_orders_2(A_158,k1_xboole_0,C_159) = k1_xboole_0
      | ~ m1_subset_1(C_159,u1_struct_0(A_158))
      | ~ l1_orders_2(A_158)
      | ~ v5_orders_2(A_158)
      | ~ v4_orders_2(A_158)
      | ~ v3_orders_2(A_158)
      | v2_struct_0(A_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_593])).

tff(c_611,plain,
    ( k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_597])).

tff(c_617,plain,
    ( k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_611])).

tff(c_619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_51,c_617])).

tff(c_620,plain,(
    ! [A_4] : ~ v1_xboole_0(A_4) ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_620,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.49  
% 3.21/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.49  %$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.21/1.49  
% 3.21/1.49  %Foreground sorts:
% 3.21/1.49  
% 3.21/1.49  
% 3.21/1.49  %Background operators:
% 3.21/1.49  
% 3.21/1.49  
% 3.21/1.49  %Foreground operators:
% 3.21/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.21/1.49  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.21/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.21/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.21/1.49  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.21/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.49  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.21/1.49  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.21/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.49  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.21/1.49  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.21/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.49  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.21/1.49  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 3.21/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.21/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.21/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.21/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.49  
% 3.21/1.51  tff(f_121, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_orders_2)).
% 3.21/1.51  tff(f_78, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.21/1.51  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 3.21/1.51  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.21/1.51  tff(f_74, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 3.21/1.51  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 3.21/1.51  tff(f_46, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.21/1.51  tff(f_104, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 3.21/1.51  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.21/1.51  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.21/1.51  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.21/1.51  tff(c_30, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.21/1.51  tff(c_18, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.21/1.51  tff(c_41, plain, (![A_34]: (k1_struct_0(A_34)=k1_xboole_0 | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.21/1.51  tff(c_46, plain, (![A_35]: (k1_struct_0(A_35)=k1_xboole_0 | ~l1_orders_2(A_35))), inference(resolution, [status(thm)], [c_18, c_41])).
% 3.21/1.51  tff(c_50, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_46])).
% 3.21/1.51  tff(c_26, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.21/1.51  tff(c_51, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_26])).
% 3.21/1.51  tff(c_36, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.21/1.51  tff(c_34, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.21/1.51  tff(c_32, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.21/1.51  tff(c_28, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.21/1.51  tff(c_8, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.21/1.51  tff(c_16, plain, (![A_12, B_13, C_14]: (m1_subset_1(k3_orders_2(A_12, B_13, C_14), k1_zfmisc_1(u1_struct_0(A_12))) | ~m1_subset_1(C_14, u1_struct_0(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_orders_2(A_12) | ~v5_orders_2(A_12) | ~v4_orders_2(A_12) | ~v3_orders_2(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.21/1.51  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.21/1.51  tff(c_114, plain, (![A_58, B_59, C_60]: (m1_subset_1(k3_orders_2(A_58, B_59, C_60), k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_subset_1(C_60, u1_struct_0(A_58)) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_orders_2(A_58) | ~v5_orders_2(A_58) | ~v4_orders_2(A_58) | ~v3_orders_2(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.21/1.51  tff(c_10, plain, (![A_5, C_7, B_6]: (m1_subset_1(A_5, C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.21/1.51  tff(c_183, plain, (![A_74, A_75, B_76, C_77]: (m1_subset_1(A_74, u1_struct_0(A_75)) | ~r2_hidden(A_74, k3_orders_2(A_75, B_76, C_77)) | ~m1_subset_1(C_77, u1_struct_0(A_75)) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_orders_2(A_75) | ~v5_orders_2(A_75) | ~v4_orders_2(A_75) | ~v3_orders_2(A_75) | v2_struct_0(A_75))), inference(resolution, [status(thm)], [c_114, c_10])).
% 3.21/1.51  tff(c_187, plain, (![A_1, A_75, B_76, C_77]: (m1_subset_1('#skF_1'(A_1, k3_orders_2(A_75, B_76, C_77)), u1_struct_0(A_75)) | ~m1_subset_1(C_77, u1_struct_0(A_75)) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_orders_2(A_75) | ~v5_orders_2(A_75) | ~v4_orders_2(A_75) | ~v3_orders_2(A_75) | v2_struct_0(A_75) | k3_orders_2(A_75, B_76, C_77)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_75, B_76, C_77), k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_4, c_183])).
% 3.21/1.51  tff(c_178, plain, (![B_70, D_71, A_72, C_73]: (r2_hidden(B_70, D_71) | ~r2_hidden(B_70, k3_orders_2(A_72, D_71, C_73)) | ~m1_subset_1(D_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~m1_subset_1(C_73, u1_struct_0(A_72)) | ~m1_subset_1(B_70, u1_struct_0(A_72)) | ~l1_orders_2(A_72) | ~v5_orders_2(A_72) | ~v4_orders_2(A_72) | ~v3_orders_2(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.21/1.51  tff(c_515, plain, (![A_143, A_144, D_145, C_146]: (r2_hidden('#skF_1'(A_143, k3_orders_2(A_144, D_145, C_146)), D_145) | ~m1_subset_1(D_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~m1_subset_1(C_146, u1_struct_0(A_144)) | ~m1_subset_1('#skF_1'(A_143, k3_orders_2(A_144, D_145, C_146)), u1_struct_0(A_144)) | ~l1_orders_2(A_144) | ~v5_orders_2(A_144) | ~v4_orders_2(A_144) | ~v3_orders_2(A_144) | v2_struct_0(A_144) | k3_orders_2(A_144, D_145, C_146)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_144, D_145, C_146), k1_zfmisc_1(A_143)))), inference(resolution, [status(thm)], [c_4, c_178])).
% 3.21/1.51  tff(c_527, plain, (![A_147, A_148, B_149, C_150]: (r2_hidden('#skF_1'(A_147, k3_orders_2(A_148, B_149, C_150)), B_149) | ~m1_subset_1(C_150, u1_struct_0(A_148)) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_orders_2(A_148) | ~v5_orders_2(A_148) | ~v4_orders_2(A_148) | ~v3_orders_2(A_148) | v2_struct_0(A_148) | k3_orders_2(A_148, B_149, C_150)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_148, B_149, C_150), k1_zfmisc_1(A_147)))), inference(resolution, [status(thm)], [c_187, c_515])).
% 3.21/1.51  tff(c_56, plain, (![C_36, B_37, A_38]: (~v1_xboole_0(C_36) | ~m1_subset_1(B_37, k1_zfmisc_1(C_36)) | ~r2_hidden(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.21/1.51  tff(c_59, plain, (![A_4, A_38]: (~v1_xboole_0(A_4) | ~r2_hidden(A_38, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_56])).
% 3.21/1.51  tff(c_64, plain, (![A_38]: (~r2_hidden(A_38, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_59])).
% 3.21/1.51  tff(c_559, plain, (![C_150, A_148, A_147]: (~m1_subset_1(C_150, u1_struct_0(A_148)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_orders_2(A_148) | ~v5_orders_2(A_148) | ~v4_orders_2(A_148) | ~v3_orders_2(A_148) | v2_struct_0(A_148) | k3_orders_2(A_148, k1_xboole_0, C_150)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_148, k1_xboole_0, C_150), k1_zfmisc_1(A_147)))), inference(resolution, [status(thm)], [c_527, c_64])).
% 3.21/1.51  tff(c_589, plain, (![C_155, A_156, A_157]: (~m1_subset_1(C_155, u1_struct_0(A_156)) | ~l1_orders_2(A_156) | ~v5_orders_2(A_156) | ~v4_orders_2(A_156) | ~v3_orders_2(A_156) | v2_struct_0(A_156) | k3_orders_2(A_156, k1_xboole_0, C_155)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_156, k1_xboole_0, C_155), k1_zfmisc_1(A_157)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_559])).
% 3.21/1.51  tff(c_593, plain, (![A_12, C_14]: (k3_orders_2(A_12, k1_xboole_0, C_14)=k1_xboole_0 | ~m1_subset_1(C_14, u1_struct_0(A_12)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_orders_2(A_12) | ~v5_orders_2(A_12) | ~v4_orders_2(A_12) | ~v3_orders_2(A_12) | v2_struct_0(A_12))), inference(resolution, [status(thm)], [c_16, c_589])).
% 3.21/1.51  tff(c_597, plain, (![A_158, C_159]: (k3_orders_2(A_158, k1_xboole_0, C_159)=k1_xboole_0 | ~m1_subset_1(C_159, u1_struct_0(A_158)) | ~l1_orders_2(A_158) | ~v5_orders_2(A_158) | ~v4_orders_2(A_158) | ~v3_orders_2(A_158) | v2_struct_0(A_158))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_593])).
% 3.21/1.51  tff(c_611, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0 | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_597])).
% 3.21/1.51  tff(c_617, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0 | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_611])).
% 3.21/1.51  tff(c_619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_51, c_617])).
% 3.21/1.51  tff(c_620, plain, (![A_4]: (~v1_xboole_0(A_4))), inference(splitRight, [status(thm)], [c_59])).
% 3.21/1.51  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.21/1.51  tff(c_622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_620, c_2])).
% 3.21/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.51  
% 3.21/1.51  Inference rules
% 3.21/1.51  ----------------------
% 3.21/1.51  #Ref     : 0
% 3.21/1.51  #Sup     : 134
% 3.21/1.51  #Fact    : 0
% 3.21/1.51  #Define  : 0
% 3.21/1.51  #Split   : 2
% 3.21/1.51  #Chain   : 0
% 3.21/1.51  #Close   : 0
% 3.21/1.51  
% 3.21/1.51  Ordering : KBO
% 3.21/1.51  
% 3.21/1.51  Simplification rules
% 3.21/1.51  ----------------------
% 3.21/1.51  #Subsume      : 63
% 3.21/1.51  #Demod        : 23
% 3.21/1.51  #Tautology    : 21
% 3.21/1.51  #SimpNegUnit  : 6
% 3.21/1.51  #BackRed      : 2
% 3.21/1.51  
% 3.21/1.51  #Partial instantiations: 0
% 3.21/1.51  #Strategies tried      : 1
% 3.21/1.51  
% 3.21/1.51  Timing (in seconds)
% 3.21/1.51  ----------------------
% 3.21/1.51  Preprocessing        : 0.29
% 3.21/1.51  Parsing              : 0.17
% 3.21/1.51  CNF conversion       : 0.02
% 3.21/1.51  Main loop            : 0.44
% 3.21/1.51  Inferencing          : 0.16
% 3.21/1.51  Reduction            : 0.11
% 3.21/1.51  Demodulation         : 0.07
% 3.21/1.51  BG Simplification    : 0.02
% 3.21/1.51  Subsumption          : 0.12
% 3.21/1.51  Abstraction          : 0.02
% 3.21/1.51  MUC search           : 0.00
% 3.21/1.51  Cooper               : 0.00
% 3.21/1.51  Total                : 0.76
% 3.21/1.51  Index Insertion      : 0.00
% 3.21/1.51  Index Deletion       : 0.00
% 3.21/1.51  Index Matching       : 0.00
% 3.21/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
