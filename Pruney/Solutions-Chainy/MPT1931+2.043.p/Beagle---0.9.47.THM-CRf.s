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
% DateTime   : Thu Dec  3 10:30:52 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   70 (  97 expanded)
%              Number of leaves         :   37 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  131 ( 235 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & l1_waybel_0(B,A) )
           => r1_waybel_0(A,B,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_28,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_waybel_0(A,B,C)
            <=> ~ r1_waybel_0(A,B,k6_subset_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C,D] :
              ( r1_tarski(C,D)
             => ( ( r1_waybel_0(A,B,C)
                 => r1_waybel_0(A,B,D) )
                & ( r2_waybel_0(A,B,C)
                 => r2_waybel_0(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_0)).

tff(f_31,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_waybel_0(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                 => ? [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                      & r1_orders_2(B,D,E)
                      & r2_hidden(k2_waybel_0(A,B,E),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_48,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_40,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_10,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(A_94,B_95)
      | ~ m1_subset_1(A_94,k1_zfmisc_1(B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_10,c_74])).

tff(c_4,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_8,plain,(
    ! [A_4,B_5] : k6_subset_1(A_4,B_5) = k4_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    ! [A_68,B_72,C_74] :
      ( r2_waybel_0(A_68,B_72,C_74)
      | r1_waybel_0(A_68,B_72,k6_subset_1(u1_struct_0(A_68),C_74))
      | ~ l1_waybel_0(B_72,A_68)
      | v2_struct_0(B_72)
      | ~ l1_struct_0(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_128,plain,(
    ! [A_135,B_136,C_137] :
      ( r2_waybel_0(A_135,B_136,C_137)
      | r1_waybel_0(A_135,B_136,k4_xboole_0(u1_struct_0(A_135),C_137))
      | ~ l1_waybel_0(B_136,A_135)
      | v2_struct_0(B_136)
      | ~ l1_struct_0(A_135)
      | v2_struct_0(A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_32])).

tff(c_140,plain,(
    ! [A_138,B_139] :
      ( r2_waybel_0(A_138,B_139,k1_xboole_0)
      | r1_waybel_0(A_138,B_139,u1_struct_0(A_138))
      | ~ l1_waybel_0(B_139,A_138)
      | v2_struct_0(B_139)
      | ~ l1_struct_0(A_138)
      | v2_struct_0(A_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_128])).

tff(c_38,plain,(
    ~ r1_waybel_0('#skF_4','#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_148,plain,
    ( r2_waybel_0('#skF_4','#skF_5',k1_xboole_0)
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_140,c_38])).

tff(c_153,plain,
    ( r2_waybel_0('#skF_4','#skF_5',k1_xboole_0)
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_148])).

tff(c_154,plain,(
    r2_waybel_0('#skF_4','#skF_5',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_46,c_153])).

tff(c_34,plain,(
    ! [A_75,B_81,D_85,C_84] :
      ( r2_waybel_0(A_75,B_81,D_85)
      | ~ r2_waybel_0(A_75,B_81,C_84)
      | ~ r1_tarski(C_84,D_85)
      | ~ l1_waybel_0(B_81,A_75)
      | v2_struct_0(B_81)
      | ~ l1_struct_0(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_156,plain,(
    ! [D_85] :
      ( r2_waybel_0('#skF_4','#skF_5',D_85)
      | ~ r1_tarski(k1_xboole_0,D_85)
      | ~ l1_waybel_0('#skF_5','#skF_4')
      | v2_struct_0('#skF_5')
      | ~ l1_struct_0('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_154,c_34])).

tff(c_159,plain,(
    ! [D_85] :
      ( r2_waybel_0('#skF_4','#skF_5',D_85)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_86,c_156])).

tff(c_160,plain,(
    ! [D_85] : r2_waybel_0('#skF_4','#skF_5',D_85) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_46,c_159])).

tff(c_6,plain,(
    ! [A_2] : m1_subset_1('#skF_1'(A_2),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_175,plain,(
    ! [A_152,B_153,C_154,D_155] :
      ( r2_hidden(k2_waybel_0(A_152,B_153,'#skF_3'(A_152,B_153,C_154,D_155)),C_154)
      | ~ m1_subset_1(D_155,u1_struct_0(B_153))
      | ~ r2_waybel_0(A_152,B_153,C_154)
      | ~ l1_waybel_0(B_153,A_152)
      | v2_struct_0(B_153)
      | ~ l1_struct_0(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_89,plain,(
    ! [C_97,B_98,A_99] :
      ( ~ v1_xboole_0(C_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(C_97))
      | ~ r2_hidden(A_99,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_98,plain,(
    ! [A_6,A_99] :
      ( ~ v1_xboole_0(A_6)
      | ~ r2_hidden(A_99,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_89])).

tff(c_101,plain,(
    ! [A_99] : ~ r2_hidden(A_99,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_197,plain,(
    ! [D_156,B_157,A_158] :
      ( ~ m1_subset_1(D_156,u1_struct_0(B_157))
      | ~ r2_waybel_0(A_158,B_157,k1_xboole_0)
      | ~ l1_waybel_0(B_157,A_158)
      | v2_struct_0(B_157)
      | ~ l1_struct_0(A_158)
      | v2_struct_0(A_158) ) ),
    inference(resolution,[status(thm)],[c_175,c_101])).

tff(c_213,plain,(
    ! [A_163,B_164] :
      ( ~ r2_waybel_0(A_163,B_164,k1_xboole_0)
      | ~ l1_waybel_0(B_164,A_163)
      | v2_struct_0(B_164)
      | ~ l1_struct_0(A_163)
      | v2_struct_0(A_163) ) ),
    inference(resolution,[status(thm)],[c_6,c_197])).

tff(c_217,plain,
    ( ~ l1_waybel_0('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_160,c_213])).

tff(c_220,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_217])).

tff(c_222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_46,c_220])).

tff(c_223,plain,(
    ! [A_6] : ~ v1_xboole_0(A_6) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.31  
% 2.22/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.31  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.22/1.31  
% 2.22/1.31  %Foreground sorts:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Background operators:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Foreground operators:
% 2.22/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.22/1.31  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.22/1.31  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.22/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.31  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.22/1.31  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.22/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.22/1.31  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.22/1.31  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.22/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.22/1.31  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.22/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.31  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.22/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.22/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.22/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.22/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.31  
% 2.22/1.32  tff(f_133, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.22/1.32  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.22/1.32  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.22/1.32  tff(f_28, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.22/1.32  tff(f_33, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.22/1.32  tff(f_93, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_waybel_0)).
% 2.22/1.32  tff(f_115, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C, D]: (r1_tarski(C, D) => ((r1_waybel_0(A, B, C) => r1_waybel_0(A, B, D)) & (r2_waybel_0(A, B, C) => r2_waybel_0(A, B, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_0)).
% 2.22/1.32  tff(f_31, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.22/1.32  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.22/1.32  tff(f_52, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.22/1.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.22/1.32  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.22/1.32  tff(c_46, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.22/1.32  tff(c_48, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.22/1.32  tff(c_40, plain, (l1_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.22/1.32  tff(c_10, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.32  tff(c_74, plain, (![A_94, B_95]: (r1_tarski(A_94, B_95) | ~m1_subset_1(A_94, k1_zfmisc_1(B_95)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.22/1.32  tff(c_86, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_10, c_74])).
% 2.22/1.32  tff(c_4, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.22/1.32  tff(c_8, plain, (![A_4, B_5]: (k6_subset_1(A_4, B_5)=k4_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.22/1.32  tff(c_32, plain, (![A_68, B_72, C_74]: (r2_waybel_0(A_68, B_72, C_74) | r1_waybel_0(A_68, B_72, k6_subset_1(u1_struct_0(A_68), C_74)) | ~l1_waybel_0(B_72, A_68) | v2_struct_0(B_72) | ~l1_struct_0(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.22/1.32  tff(c_128, plain, (![A_135, B_136, C_137]: (r2_waybel_0(A_135, B_136, C_137) | r1_waybel_0(A_135, B_136, k4_xboole_0(u1_struct_0(A_135), C_137)) | ~l1_waybel_0(B_136, A_135) | v2_struct_0(B_136) | ~l1_struct_0(A_135) | v2_struct_0(A_135))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_32])).
% 2.22/1.32  tff(c_140, plain, (![A_138, B_139]: (r2_waybel_0(A_138, B_139, k1_xboole_0) | r1_waybel_0(A_138, B_139, u1_struct_0(A_138)) | ~l1_waybel_0(B_139, A_138) | v2_struct_0(B_139) | ~l1_struct_0(A_138) | v2_struct_0(A_138))), inference(superposition, [status(thm), theory('equality')], [c_4, c_128])).
% 2.22/1.32  tff(c_38, plain, (~r1_waybel_0('#skF_4', '#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.22/1.32  tff(c_148, plain, (r2_waybel_0('#skF_4', '#skF_5', k1_xboole_0) | ~l1_waybel_0('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_140, c_38])).
% 2.22/1.32  tff(c_153, plain, (r2_waybel_0('#skF_4', '#skF_5', k1_xboole_0) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_148])).
% 2.22/1.32  tff(c_154, plain, (r2_waybel_0('#skF_4', '#skF_5', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_50, c_46, c_153])).
% 2.22/1.32  tff(c_34, plain, (![A_75, B_81, D_85, C_84]: (r2_waybel_0(A_75, B_81, D_85) | ~r2_waybel_0(A_75, B_81, C_84) | ~r1_tarski(C_84, D_85) | ~l1_waybel_0(B_81, A_75) | v2_struct_0(B_81) | ~l1_struct_0(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.22/1.32  tff(c_156, plain, (![D_85]: (r2_waybel_0('#skF_4', '#skF_5', D_85) | ~r1_tarski(k1_xboole_0, D_85) | ~l1_waybel_0('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_154, c_34])).
% 2.22/1.32  tff(c_159, plain, (![D_85]: (r2_waybel_0('#skF_4', '#skF_5', D_85) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_86, c_156])).
% 2.22/1.32  tff(c_160, plain, (![D_85]: (r2_waybel_0('#skF_4', '#skF_5', D_85))), inference(negUnitSimplification, [status(thm)], [c_50, c_46, c_159])).
% 2.22/1.32  tff(c_6, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.32  tff(c_175, plain, (![A_152, B_153, C_154, D_155]: (r2_hidden(k2_waybel_0(A_152, B_153, '#skF_3'(A_152, B_153, C_154, D_155)), C_154) | ~m1_subset_1(D_155, u1_struct_0(B_153)) | ~r2_waybel_0(A_152, B_153, C_154) | ~l1_waybel_0(B_153, A_152) | v2_struct_0(B_153) | ~l1_struct_0(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.22/1.32  tff(c_89, plain, (![C_97, B_98, A_99]: (~v1_xboole_0(C_97) | ~m1_subset_1(B_98, k1_zfmisc_1(C_97)) | ~r2_hidden(A_99, B_98))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.22/1.32  tff(c_98, plain, (![A_6, A_99]: (~v1_xboole_0(A_6) | ~r2_hidden(A_99, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_89])).
% 2.22/1.32  tff(c_101, plain, (![A_99]: (~r2_hidden(A_99, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_98])).
% 2.22/1.32  tff(c_197, plain, (![D_156, B_157, A_158]: (~m1_subset_1(D_156, u1_struct_0(B_157)) | ~r2_waybel_0(A_158, B_157, k1_xboole_0) | ~l1_waybel_0(B_157, A_158) | v2_struct_0(B_157) | ~l1_struct_0(A_158) | v2_struct_0(A_158))), inference(resolution, [status(thm)], [c_175, c_101])).
% 2.22/1.32  tff(c_213, plain, (![A_163, B_164]: (~r2_waybel_0(A_163, B_164, k1_xboole_0) | ~l1_waybel_0(B_164, A_163) | v2_struct_0(B_164) | ~l1_struct_0(A_163) | v2_struct_0(A_163))), inference(resolution, [status(thm)], [c_6, c_197])).
% 2.22/1.32  tff(c_217, plain, (~l1_waybel_0('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_160, c_213])).
% 2.22/1.32  tff(c_220, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_217])).
% 2.22/1.32  tff(c_222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_46, c_220])).
% 2.22/1.32  tff(c_223, plain, (![A_6]: (~v1_xboole_0(A_6))), inference(splitRight, [status(thm)], [c_98])).
% 2.22/1.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.22/1.32  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_223, c_2])).
% 2.22/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.32  
% 2.22/1.32  Inference rules
% 2.22/1.32  ----------------------
% 2.22/1.32  #Ref     : 0
% 2.22/1.32  #Sup     : 33
% 2.22/1.32  #Fact    : 0
% 2.22/1.32  #Define  : 0
% 2.22/1.32  #Split   : 1
% 2.22/1.32  #Chain   : 0
% 2.22/1.32  #Close   : 0
% 2.22/1.32  
% 2.22/1.32  Ordering : KBO
% 2.22/1.32  
% 2.22/1.32  Simplification rules
% 2.22/1.32  ----------------------
% 2.22/1.32  #Subsume      : 6
% 2.22/1.32  #Demod        : 13
% 2.22/1.32  #Tautology    : 9
% 2.22/1.32  #SimpNegUnit  : 5
% 2.22/1.32  #BackRed      : 1
% 2.22/1.33  
% 2.22/1.33  #Partial instantiations: 0
% 2.22/1.33  #Strategies tried      : 1
% 2.22/1.33  
% 2.22/1.33  Timing (in seconds)
% 2.22/1.33  ----------------------
% 2.51/1.33  Preprocessing        : 0.32
% 2.51/1.33  Parsing              : 0.17
% 2.51/1.33  CNF conversion       : 0.03
% 2.51/1.33  Main loop            : 0.21
% 2.51/1.33  Inferencing          : 0.08
% 2.51/1.33  Reduction            : 0.06
% 2.51/1.33  Demodulation         : 0.04
% 2.51/1.33  BG Simplification    : 0.01
% 2.51/1.33  Subsumption          : 0.03
% 2.51/1.33  Abstraction          : 0.01
% 2.51/1.33  MUC search           : 0.00
% 2.51/1.33  Cooper               : 0.00
% 2.51/1.33  Total                : 0.56
% 2.51/1.33  Index Insertion      : 0.00
% 2.51/1.33  Index Deletion       : 0.00
% 2.51/1.33  Index Matching       : 0.00
% 2.51/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
