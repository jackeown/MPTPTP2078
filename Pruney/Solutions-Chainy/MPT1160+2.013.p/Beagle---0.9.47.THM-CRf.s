%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:45 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   63 (  80 expanded)
%              Number of leaves         :   31 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :  149 ( 215 expanded)
%              Number of equality atoms :   16 (  25 expanded)
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

tff(f_117,negated_conjecture,(
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

tff(f_74,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_70,axiom,(
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

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_100,axiom,(
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

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_28,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_16,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_39,plain,(
    ! [A_33] :
      ( k1_struct_0(A_33) = k1_xboole_0
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_44,plain,(
    ! [A_34] :
      ( k1_struct_0(A_34) = k1_xboole_0
      | ~ l1_orders_2(A_34) ) ),
    inference(resolution,[status(thm)],[c_16,c_39])).

tff(c_48,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_44])).

tff(c_24,plain,(
    k3_orders_2('#skF_2',k1_struct_0('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_49,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_24])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_34,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_32,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_30,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [A_43,B_44,C_45] :
      ( m1_subset_1(k3_orders_2(A_43,B_44,C_45),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_subset_1(C_45,u1_struct_0(A_43))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_orders_2(A_43)
      | ~ v5_orders_2(A_43)
      | ~ v4_orders_2(A_43)
      | ~ v3_orders_2(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_4,C_6,B_5] :
      ( m1_subset_1(A_4,C_6)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(C_6))
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_91,plain,(
    ! [A_53,A_54,B_55,C_56] :
      ( m1_subset_1(A_53,u1_struct_0(A_54))
      | ~ r2_hidden(A_53,k3_orders_2(A_54,B_55,C_56))
      | ~ m1_subset_1(C_56,u1_struct_0(A_54))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_orders_2(A_54)
      | ~ v5_orders_2(A_54)
      | ~ v4_orders_2(A_54)
      | ~ v3_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_71,c_8])).

tff(c_95,plain,(
    ! [A_54,B_55,C_56] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_54,B_55,C_56)),u1_struct_0(A_54))
      | ~ m1_subset_1(C_56,u1_struct_0(A_54))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_orders_2(A_54)
      | ~ v5_orders_2(A_54)
      | ~ v4_orders_2(A_54)
      | ~ v3_orders_2(A_54)
      | v2_struct_0(A_54)
      | k3_orders_2(A_54,B_55,C_56) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_96,plain,(
    ! [B_57,D_58,A_59,C_60] :
      ( r2_hidden(B_57,D_58)
      | ~ r2_hidden(B_57,k3_orders_2(A_59,D_58,C_60))
      | ~ m1_subset_1(D_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_subset_1(C_60,u1_struct_0(A_59))
      | ~ m1_subset_1(B_57,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59)
      | ~ v5_orders_2(A_59)
      | ~ v4_orders_2(A_59)
      | ~ v3_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_118,plain,(
    ! [A_72,D_73,C_74] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_72,D_73,C_74)),D_73)
      | ~ m1_subset_1(D_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ m1_subset_1(C_74,u1_struct_0(A_72))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_72,D_73,C_74)),u1_struct_0(A_72))
      | ~ l1_orders_2(A_72)
      | ~ v5_orders_2(A_72)
      | ~ v4_orders_2(A_72)
      | ~ v3_orders_2(A_72)
      | v2_struct_0(A_72)
      | k3_orders_2(A_72,D_73,C_74) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_96])).

tff(c_122,plain,(
    ! [A_75,B_76,C_77] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_75,B_76,C_77)),B_76)
      | ~ m1_subset_1(C_77,u1_struct_0(A_75))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_orders_2(A_75)
      | ~ v5_orders_2(A_75)
      | ~ v4_orders_2(A_75)
      | ~ v3_orders_2(A_75)
      | v2_struct_0(A_75)
      | k3_orders_2(A_75,B_76,C_77) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_95,c_118])).

tff(c_55,plain,(
    ! [C_36,B_37,A_38] :
      ( ~ v1_xboole_0(C_36)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(C_36))
      | ~ r2_hidden(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_58,plain,(
    ! [A_3,A_38] :
      ( ~ v1_xboole_0(A_3)
      | ~ r2_hidden(A_38,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_55])).

tff(c_59,plain,(
    ! [A_38] : ~ r2_hidden(A_38,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_138,plain,(
    ! [C_77,A_75] :
      ( ~ m1_subset_1(C_77,u1_struct_0(A_75))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_orders_2(A_75)
      | ~ v5_orders_2(A_75)
      | ~ v4_orders_2(A_75)
      | ~ v3_orders_2(A_75)
      | v2_struct_0(A_75)
      | k3_orders_2(A_75,k1_xboole_0,C_77) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_122,c_59])).

tff(c_146,plain,(
    ! [C_78,A_79] :
      ( ~ m1_subset_1(C_78,u1_struct_0(A_79))
      | ~ l1_orders_2(A_79)
      | ~ v5_orders_2(A_79)
      | ~ v4_orders_2(A_79)
      | ~ v3_orders_2(A_79)
      | v2_struct_0(A_79)
      | k3_orders_2(A_79,k1_xboole_0,C_78) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_138])).

tff(c_152,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_146])).

tff(c_156,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_152])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_36,c_156])).

tff(c_159,plain,(
    ! [A_3] : ~ v1_xboole_0(A_3) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:16:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.50  
% 2.55/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.50  %$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.55/1.50  
% 2.55/1.50  %Foreground sorts:
% 2.55/1.50  
% 2.55/1.50  
% 2.55/1.50  %Background operators:
% 2.55/1.50  
% 2.55/1.50  
% 2.55/1.50  %Foreground operators:
% 2.55/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.55/1.50  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.55/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.55/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.55/1.50  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.55/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.50  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.55/1.50  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.55/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.55/1.50  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.55/1.50  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.55/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.50  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.55/1.50  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.55/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.55/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.55/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.50  
% 2.76/1.52  tff(f_117, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_orders_2)).
% 2.76/1.52  tff(f_74, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.76/1.52  tff(f_53, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 2.76/1.52  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.76/1.52  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.76/1.52  tff(f_70, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 2.76/1.52  tff(f_42, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.76/1.52  tff(f_100, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 2.76/1.52  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.76/1.52  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.76/1.52  tff(c_28, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.76/1.52  tff(c_16, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.76/1.52  tff(c_39, plain, (![A_33]: (k1_struct_0(A_33)=k1_xboole_0 | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.76/1.52  tff(c_44, plain, (![A_34]: (k1_struct_0(A_34)=k1_xboole_0 | ~l1_orders_2(A_34))), inference(resolution, [status(thm)], [c_16, c_39])).
% 2.76/1.52  tff(c_48, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_44])).
% 2.76/1.52  tff(c_24, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.76/1.52  tff(c_49, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_24])).
% 2.76/1.52  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.76/1.52  tff(c_34, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.76/1.52  tff(c_32, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.76/1.52  tff(c_30, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.76/1.52  tff(c_26, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.76/1.52  tff(c_6, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.76/1.52  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.76/1.52  tff(c_71, plain, (![A_43, B_44, C_45]: (m1_subset_1(k3_orders_2(A_43, B_44, C_45), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_subset_1(C_45, u1_struct_0(A_43)) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_orders_2(A_43) | ~v5_orders_2(A_43) | ~v4_orders_2(A_43) | ~v3_orders_2(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.76/1.52  tff(c_8, plain, (![A_4, C_6, B_5]: (m1_subset_1(A_4, C_6) | ~m1_subset_1(B_5, k1_zfmisc_1(C_6)) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.76/1.52  tff(c_91, plain, (![A_53, A_54, B_55, C_56]: (m1_subset_1(A_53, u1_struct_0(A_54)) | ~r2_hidden(A_53, k3_orders_2(A_54, B_55, C_56)) | ~m1_subset_1(C_56, u1_struct_0(A_54)) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_orders_2(A_54) | ~v5_orders_2(A_54) | ~v4_orders_2(A_54) | ~v3_orders_2(A_54) | v2_struct_0(A_54))), inference(resolution, [status(thm)], [c_71, c_8])).
% 2.76/1.52  tff(c_95, plain, (![A_54, B_55, C_56]: (m1_subset_1('#skF_1'(k3_orders_2(A_54, B_55, C_56)), u1_struct_0(A_54)) | ~m1_subset_1(C_56, u1_struct_0(A_54)) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_orders_2(A_54) | ~v5_orders_2(A_54) | ~v4_orders_2(A_54) | ~v3_orders_2(A_54) | v2_struct_0(A_54) | k3_orders_2(A_54, B_55, C_56)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_91])).
% 2.76/1.52  tff(c_96, plain, (![B_57, D_58, A_59, C_60]: (r2_hidden(B_57, D_58) | ~r2_hidden(B_57, k3_orders_2(A_59, D_58, C_60)) | ~m1_subset_1(D_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_subset_1(C_60, u1_struct_0(A_59)) | ~m1_subset_1(B_57, u1_struct_0(A_59)) | ~l1_orders_2(A_59) | ~v5_orders_2(A_59) | ~v4_orders_2(A_59) | ~v3_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.76/1.52  tff(c_118, plain, (![A_72, D_73, C_74]: (r2_hidden('#skF_1'(k3_orders_2(A_72, D_73, C_74)), D_73) | ~m1_subset_1(D_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~m1_subset_1(C_74, u1_struct_0(A_72)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_72, D_73, C_74)), u1_struct_0(A_72)) | ~l1_orders_2(A_72) | ~v5_orders_2(A_72) | ~v4_orders_2(A_72) | ~v3_orders_2(A_72) | v2_struct_0(A_72) | k3_orders_2(A_72, D_73, C_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_96])).
% 2.76/1.52  tff(c_122, plain, (![A_75, B_76, C_77]: (r2_hidden('#skF_1'(k3_orders_2(A_75, B_76, C_77)), B_76) | ~m1_subset_1(C_77, u1_struct_0(A_75)) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_orders_2(A_75) | ~v5_orders_2(A_75) | ~v4_orders_2(A_75) | ~v3_orders_2(A_75) | v2_struct_0(A_75) | k3_orders_2(A_75, B_76, C_77)=k1_xboole_0)), inference(resolution, [status(thm)], [c_95, c_118])).
% 2.76/1.52  tff(c_55, plain, (![C_36, B_37, A_38]: (~v1_xboole_0(C_36) | ~m1_subset_1(B_37, k1_zfmisc_1(C_36)) | ~r2_hidden(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.76/1.52  tff(c_58, plain, (![A_3, A_38]: (~v1_xboole_0(A_3) | ~r2_hidden(A_38, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_55])).
% 2.76/1.52  tff(c_59, plain, (![A_38]: (~r2_hidden(A_38, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_58])).
% 2.76/1.52  tff(c_138, plain, (![C_77, A_75]: (~m1_subset_1(C_77, u1_struct_0(A_75)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_orders_2(A_75) | ~v5_orders_2(A_75) | ~v4_orders_2(A_75) | ~v3_orders_2(A_75) | v2_struct_0(A_75) | k3_orders_2(A_75, k1_xboole_0, C_77)=k1_xboole_0)), inference(resolution, [status(thm)], [c_122, c_59])).
% 2.76/1.52  tff(c_146, plain, (![C_78, A_79]: (~m1_subset_1(C_78, u1_struct_0(A_79)) | ~l1_orders_2(A_79) | ~v5_orders_2(A_79) | ~v4_orders_2(A_79) | ~v3_orders_2(A_79) | v2_struct_0(A_79) | k3_orders_2(A_79, k1_xboole_0, C_78)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_138])).
% 2.76/1.52  tff(c_152, plain, (~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_146])).
% 2.76/1.52  tff(c_156, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_152])).
% 2.76/1.52  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_36, c_156])).
% 2.76/1.52  tff(c_159, plain, (![A_3]: (~v1_xboole_0(A_3))), inference(splitRight, [status(thm)], [c_58])).
% 2.76/1.52  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.76/1.52  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_2])).
% 2.76/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.52  
% 2.76/1.52  Inference rules
% 2.76/1.52  ----------------------
% 2.76/1.52  #Ref     : 0
% 2.76/1.52  #Sup     : 25
% 2.76/1.52  #Fact    : 0
% 2.76/1.52  #Define  : 0
% 2.76/1.52  #Split   : 2
% 2.76/1.52  #Chain   : 0
% 2.76/1.52  #Close   : 0
% 2.76/1.52  
% 2.76/1.52  Ordering : KBO
% 2.76/1.52  
% 2.76/1.52  Simplification rules
% 2.76/1.52  ----------------------
% 2.76/1.52  #Subsume      : 5
% 2.76/1.52  #Demod        : 10
% 2.76/1.52  #Tautology    : 3
% 2.76/1.52  #SimpNegUnit  : 3
% 2.76/1.52  #BackRed      : 2
% 2.76/1.52  
% 2.76/1.52  #Partial instantiations: 0
% 2.76/1.52  #Strategies tried      : 1
% 2.76/1.52  
% 2.76/1.52  Timing (in seconds)
% 2.76/1.52  ----------------------
% 2.76/1.52  Preprocessing        : 0.39
% 2.76/1.52  Parsing              : 0.19
% 2.76/1.52  CNF conversion       : 0.04
% 2.76/1.52  Main loop            : 0.26
% 2.76/1.52  Inferencing          : 0.10
% 2.76/1.52  Reduction            : 0.06
% 2.76/1.52  Demodulation         : 0.04
% 2.76/1.52  BG Simplification    : 0.02
% 2.76/1.52  Subsumption          : 0.06
% 2.76/1.52  Abstraction          : 0.01
% 2.76/1.52  MUC search           : 0.00
% 2.76/1.52  Cooper               : 0.00
% 2.76/1.53  Total                : 0.69
% 2.76/1.53  Index Insertion      : 0.00
% 2.76/1.53  Index Deletion       : 0.00
% 2.76/1.53  Index Matching       : 0.00
% 2.76/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
