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
% DateTime   : Thu Dec  3 10:19:46 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   66 (  83 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  155 ( 221 expanded)
%              Number of equality atoms :   17 (  26 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

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

tff(c_30,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_18,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_47,plain,(
    ! [A_35] :
      ( v1_xboole_0(k1_struct_0(A_35))
      | ~ l1_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_52,plain,(
    ! [A_36] :
      ( k1_struct_0(A_36) = k1_xboole_0
      | ~ l1_struct_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_47,c_6])).

tff(c_57,plain,(
    ! [A_37] :
      ( k1_struct_0(A_37) = k1_xboole_0
      | ~ l1_orders_2(A_37) ) ),
    inference(resolution,[status(thm)],[c_18,c_52])).

tff(c_61,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_57])).

tff(c_26,plain,(
    k3_orders_2('#skF_2',k1_struct_0('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_62,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_26])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

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

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_88,plain,(
    ! [A_46,B_47,C_48] :
      ( m1_subset_1(k3_orders_2(A_46,B_47,C_48),k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ m1_subset_1(C_48,u1_struct_0(A_46))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_orders_2(A_46)
      | ~ v5_orders_2(A_46)
      | ~ v4_orders_2(A_46)
      | ~ v3_orders_2(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( m1_subset_1(A_5,C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_113,plain,(
    ! [A_60,A_61,B_62,C_63] :
      ( m1_subset_1(A_60,u1_struct_0(A_61))
      | ~ r2_hidden(A_60,k3_orders_2(A_61,B_62,C_63))
      | ~ m1_subset_1(C_63,u1_struct_0(A_61))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_orders_2(A_61)
      | ~ v5_orders_2(A_61)
      | ~ v4_orders_2(A_61)
      | ~ v3_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_88,c_10])).

tff(c_117,plain,(
    ! [A_61,B_62,C_63] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_61,B_62,C_63)),u1_struct_0(A_61))
      | ~ m1_subset_1(C_63,u1_struct_0(A_61))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_orders_2(A_61)
      | ~ v5_orders_2(A_61)
      | ~ v4_orders_2(A_61)
      | ~ v3_orders_2(A_61)
      | v2_struct_0(A_61)
      | k3_orders_2(A_61,B_62,C_63) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_113])).

tff(c_107,plain,(
    ! [B_56,D_57,A_58,C_59] :
      ( r2_hidden(B_56,D_57)
      | ~ r2_hidden(B_56,k3_orders_2(A_58,D_57,C_59))
      | ~ m1_subset_1(D_57,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_subset_1(C_59,u1_struct_0(A_58))
      | ~ m1_subset_1(B_56,u1_struct_0(A_58))
      | ~ l1_orders_2(A_58)
      | ~ v5_orders_2(A_58)
      | ~ v4_orders_2(A_58)
      | ~ v3_orders_2(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_135,plain,(
    ! [A_75,D_76,C_77] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_75,D_76,C_77)),D_76)
      | ~ m1_subset_1(D_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ m1_subset_1(C_77,u1_struct_0(A_75))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_75,D_76,C_77)),u1_struct_0(A_75))
      | ~ l1_orders_2(A_75)
      | ~ v5_orders_2(A_75)
      | ~ v4_orders_2(A_75)
      | ~ v3_orders_2(A_75)
      | v2_struct_0(A_75)
      | k3_orders_2(A_75,D_76,C_77) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_107])).

tff(c_139,plain,(
    ! [A_78,B_79,C_80] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_78,B_79,C_80)),B_79)
      | ~ m1_subset_1(C_80,u1_struct_0(A_78))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78)
      | k3_orders_2(A_78,B_79,C_80) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_117,c_135])).

tff(c_72,plain,(
    ! [C_39,B_40,A_41] :
      ( ~ v1_xboole_0(C_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_39))
      | ~ r2_hidden(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_75,plain,(
    ! [A_4,A_41] :
      ( ~ v1_xboole_0(A_4)
      | ~ r2_hidden(A_41,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_72])).

tff(c_76,plain,(
    ! [A_41] : ~ r2_hidden(A_41,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_155,plain,(
    ! [C_80,A_78] :
      ( ~ m1_subset_1(C_80,u1_struct_0(A_78))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78)
      | k3_orders_2(A_78,k1_xboole_0,C_80) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_139,c_76])).

tff(c_163,plain,(
    ! [C_81,A_82] :
      ( ~ m1_subset_1(C_81,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82)
      | ~ v4_orders_2(A_82)
      | ~ v3_orders_2(A_82)
      | v2_struct_0(A_82)
      | k3_orders_2(A_82,k1_xboole_0,C_81) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_155])).

tff(c_169,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_163])).

tff(c_173,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_169])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_38,c_173])).

tff(c_176,plain,(
    ! [A_4] : ~ v1_xboole_0(A_4) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.29  
% 2.16/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.29  %$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.16/1.29  
% 2.16/1.29  %Foreground sorts:
% 2.16/1.29  
% 2.16/1.29  
% 2.16/1.29  %Background operators:
% 2.16/1.29  
% 2.16/1.29  
% 2.16/1.29  %Foreground operators:
% 2.16/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.16/1.29  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.16/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.29  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.16/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.29  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.16/1.29  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.16/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.16/1.29  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.29  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.16/1.29  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.16/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.16/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.29  
% 2.16/1.31  tff(f_121, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_orders_2)).
% 2.16/1.31  tff(f_78, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.16/1.31  tff(f_57, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_struct_0)).
% 2.16/1.31  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 2.16/1.31  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.16/1.31  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.16/1.31  tff(f_74, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 2.16/1.31  tff(f_46, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.16/1.31  tff(f_104, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 2.16/1.31  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.16/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.16/1.31  tff(c_30, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.16/1.31  tff(c_18, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.16/1.31  tff(c_47, plain, (![A_35]: (v1_xboole_0(k1_struct_0(A_35)) | ~l1_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.16/1.31  tff(c_6, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.16/1.31  tff(c_52, plain, (![A_36]: (k1_struct_0(A_36)=k1_xboole_0 | ~l1_struct_0(A_36))), inference(resolution, [status(thm)], [c_47, c_6])).
% 2.16/1.31  tff(c_57, plain, (![A_37]: (k1_struct_0(A_37)=k1_xboole_0 | ~l1_orders_2(A_37))), inference(resolution, [status(thm)], [c_18, c_52])).
% 2.16/1.31  tff(c_61, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_57])).
% 2.16/1.31  tff(c_26, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.16/1.31  tff(c_62, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_61, c_26])).
% 2.16/1.31  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.16/1.31  tff(c_36, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.16/1.31  tff(c_34, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.16/1.31  tff(c_32, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.16/1.31  tff(c_28, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.16/1.31  tff(c_8, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.16/1.31  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.16/1.31  tff(c_88, plain, (![A_46, B_47, C_48]: (m1_subset_1(k3_orders_2(A_46, B_47, C_48), k1_zfmisc_1(u1_struct_0(A_46))) | ~m1_subset_1(C_48, u1_struct_0(A_46)) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_orders_2(A_46) | ~v5_orders_2(A_46) | ~v4_orders_2(A_46) | ~v3_orders_2(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.16/1.31  tff(c_10, plain, (![A_5, C_7, B_6]: (m1_subset_1(A_5, C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.16/1.31  tff(c_113, plain, (![A_60, A_61, B_62, C_63]: (m1_subset_1(A_60, u1_struct_0(A_61)) | ~r2_hidden(A_60, k3_orders_2(A_61, B_62, C_63)) | ~m1_subset_1(C_63, u1_struct_0(A_61)) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_orders_2(A_61) | ~v5_orders_2(A_61) | ~v4_orders_2(A_61) | ~v3_orders_2(A_61) | v2_struct_0(A_61))), inference(resolution, [status(thm)], [c_88, c_10])).
% 2.16/1.31  tff(c_117, plain, (![A_61, B_62, C_63]: (m1_subset_1('#skF_1'(k3_orders_2(A_61, B_62, C_63)), u1_struct_0(A_61)) | ~m1_subset_1(C_63, u1_struct_0(A_61)) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_orders_2(A_61) | ~v5_orders_2(A_61) | ~v4_orders_2(A_61) | ~v3_orders_2(A_61) | v2_struct_0(A_61) | k3_orders_2(A_61, B_62, C_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_113])).
% 2.16/1.31  tff(c_107, plain, (![B_56, D_57, A_58, C_59]: (r2_hidden(B_56, D_57) | ~r2_hidden(B_56, k3_orders_2(A_58, D_57, C_59)) | ~m1_subset_1(D_57, k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_subset_1(C_59, u1_struct_0(A_58)) | ~m1_subset_1(B_56, u1_struct_0(A_58)) | ~l1_orders_2(A_58) | ~v5_orders_2(A_58) | ~v4_orders_2(A_58) | ~v3_orders_2(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.16/1.31  tff(c_135, plain, (![A_75, D_76, C_77]: (r2_hidden('#skF_1'(k3_orders_2(A_75, D_76, C_77)), D_76) | ~m1_subset_1(D_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~m1_subset_1(C_77, u1_struct_0(A_75)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_75, D_76, C_77)), u1_struct_0(A_75)) | ~l1_orders_2(A_75) | ~v5_orders_2(A_75) | ~v4_orders_2(A_75) | ~v3_orders_2(A_75) | v2_struct_0(A_75) | k3_orders_2(A_75, D_76, C_77)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_107])).
% 2.16/1.31  tff(c_139, plain, (![A_78, B_79, C_80]: (r2_hidden('#skF_1'(k3_orders_2(A_78, B_79, C_80)), B_79) | ~m1_subset_1(C_80, u1_struct_0(A_78)) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78) | k3_orders_2(A_78, B_79, C_80)=k1_xboole_0)), inference(resolution, [status(thm)], [c_117, c_135])).
% 2.16/1.31  tff(c_72, plain, (![C_39, B_40, A_41]: (~v1_xboole_0(C_39) | ~m1_subset_1(B_40, k1_zfmisc_1(C_39)) | ~r2_hidden(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.16/1.31  tff(c_75, plain, (![A_4, A_41]: (~v1_xboole_0(A_4) | ~r2_hidden(A_41, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_72])).
% 2.16/1.31  tff(c_76, plain, (![A_41]: (~r2_hidden(A_41, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_75])).
% 2.16/1.31  tff(c_155, plain, (![C_80, A_78]: (~m1_subset_1(C_80, u1_struct_0(A_78)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78) | k3_orders_2(A_78, k1_xboole_0, C_80)=k1_xboole_0)), inference(resolution, [status(thm)], [c_139, c_76])).
% 2.16/1.31  tff(c_163, plain, (![C_81, A_82]: (~m1_subset_1(C_81, u1_struct_0(A_82)) | ~l1_orders_2(A_82) | ~v5_orders_2(A_82) | ~v4_orders_2(A_82) | ~v3_orders_2(A_82) | v2_struct_0(A_82) | k3_orders_2(A_82, k1_xboole_0, C_81)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_155])).
% 2.16/1.31  tff(c_169, plain, (~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_163])).
% 2.16/1.31  tff(c_173, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_169])).
% 2.16/1.31  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_38, c_173])).
% 2.16/1.31  tff(c_176, plain, (![A_4]: (~v1_xboole_0(A_4))), inference(splitRight, [status(thm)], [c_75])).
% 2.16/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.16/1.31  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_2])).
% 2.16/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.31  
% 2.16/1.31  Inference rules
% 2.16/1.31  ----------------------
% 2.16/1.31  #Ref     : 0
% 2.16/1.31  #Sup     : 29
% 2.16/1.31  #Fact    : 0
% 2.16/1.31  #Define  : 0
% 2.16/1.31  #Split   : 2
% 2.16/1.31  #Chain   : 0
% 2.16/1.31  #Close   : 0
% 2.16/1.31  
% 2.16/1.31  Ordering : KBO
% 2.16/1.31  
% 2.16/1.31  Simplification rules
% 2.16/1.31  ----------------------
% 2.16/1.31  #Subsume      : 6
% 2.16/1.31  #Demod        : 11
% 2.16/1.31  #Tautology    : 5
% 2.16/1.31  #SimpNegUnit  : 4
% 2.16/1.31  #BackRed      : 3
% 2.16/1.31  
% 2.16/1.31  #Partial instantiations: 0
% 2.16/1.31  #Strategies tried      : 1
% 2.16/1.31  
% 2.16/1.31  Timing (in seconds)
% 2.16/1.31  ----------------------
% 2.16/1.31  Preprocessing        : 0.32
% 2.16/1.31  Parsing              : 0.18
% 2.16/1.31  CNF conversion       : 0.02
% 2.16/1.31  Main loop            : 0.22
% 2.16/1.31  Inferencing          : 0.09
% 2.16/1.31  Reduction            : 0.06
% 2.16/1.31  Demodulation         : 0.04
% 2.16/1.31  BG Simplification    : 0.01
% 2.16/1.31  Subsumption          : 0.05
% 2.16/1.31  Abstraction          : 0.01
% 2.16/1.31  MUC search           : 0.00
% 2.16/1.31  Cooper               : 0.00
% 2.16/1.31  Total                : 0.58
% 2.16/1.31  Index Insertion      : 0.00
% 2.16/1.31  Index Deletion       : 0.00
% 2.16/1.31  Index Matching       : 0.00
% 2.16/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
