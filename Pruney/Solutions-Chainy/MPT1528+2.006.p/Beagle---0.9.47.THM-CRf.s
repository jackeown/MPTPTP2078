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
% DateTime   : Thu Dec  3 10:24:57 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   64 (  90 expanded)
%              Number of leaves         :   30 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   88 ( 153 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > l1_orders_2 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( r2_lattice3(A,k1_xboole_0,B)
              & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_60,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

tff(f_62,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_248,plain,(
    ! [A_110,B_111] :
      ( r2_hidden('#skF_1'(A_110,B_111),A_110)
      | r1_xboole_0(A_110,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_260,plain,(
    ! [A_114,B_115,B_116] :
      ( ~ r1_xboole_0(A_114,B_115)
      | r1_xboole_0(k3_xboole_0(A_114,B_115),B_116) ) ),
    inference(resolution,[status(thm)],[c_248,c_12])).

tff(c_38,plain,
    ( ~ r1_lattice3('#skF_5',k1_xboole_0,'#skF_6')
    | ~ r2_lattice3('#skF_5',k1_xboole_0,'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_57,plain,(
    ~ r2_lattice3('#skF_5',k1_xboole_0,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_42,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_125,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_hidden('#skF_4'(A_73,B_74,C_75),B_74)
      | r2_lattice3(A_73,B_74,C_75)
      | ~ m1_subset_1(C_75,u1_struct_0(A_73))
      | ~ l1_orders_2(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_14,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_51,plain,(
    ! [A_46,B_47,C_48] :
      ( ~ r1_xboole_0(A_46,B_47)
      | ~ r2_hidden(C_48,k3_xboole_0(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_54,plain,(
    ! [A_11,C_48] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_48,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_51])).

tff(c_55,plain,(
    ! [C_48] : ~ r2_hidden(C_48,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_136,plain,(
    ! [A_76,C_77] :
      ( r2_lattice3(A_76,k1_xboole_0,C_77)
      | ~ m1_subset_1(C_77,u1_struct_0(A_76))
      | ~ l1_orders_2(A_76) ) ),
    inference(resolution,[status(thm)],[c_125,c_55])).

tff(c_139,plain,
    ( r2_lattice3('#skF_5',k1_xboole_0,'#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_136])).

tff(c_142,plain,(
    r2_lattice3('#skF_5',k1_xboole_0,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_139])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_142])).

tff(c_145,plain,(
    ~ r1_lattice3('#skF_5',k1_xboole_0,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_214,plain,(
    ! [A_101,B_102,C_103] :
      ( r2_hidden('#skF_3'(A_101,B_102,C_103),B_102)
      | r1_lattice3(A_101,B_102,C_103)
      | ~ m1_subset_1(C_103,u1_struct_0(A_101))
      | ~ l1_orders_2(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_236,plain,(
    ! [A_107,C_108] :
      ( r1_lattice3(A_107,k1_xboole_0,C_108)
      | ~ m1_subset_1(C_108,u1_struct_0(A_107))
      | ~ l1_orders_2(A_107) ) ),
    inference(resolution,[status(thm)],[c_214,c_55])).

tff(c_239,plain,
    ( r1_lattice3('#skF_5',k1_xboole_0,'#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_236])).

tff(c_242,plain,(
    r1_lattice3('#skF_5',k1_xboole_0,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_239])).

tff(c_244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_242])).

tff(c_245,plain,(
    ! [A_11] : ~ r1_xboole_0(A_11,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_267,plain,(
    ! [A_114,B_115] : ~ r1_xboole_0(A_114,B_115) ),
    inference(resolution,[status(thm)],[c_260,c_245])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_270,plain,(
    ! [A_1,B_2] : r2_hidden('#skF_1'(A_1,B_2),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_267,c_8])).

tff(c_16,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_275,plain,(
    ! [C_123,B_124,A_125] :
      ( ~ v1_xboole_0(C_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(C_123))
      | ~ r2_hidden(A_125,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_278,plain,(
    ! [A_12,A_125] :
      ( ~ v1_xboole_0(A_12)
      | ~ r2_hidden(A_125,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_275])).

tff(c_280,plain,(
    ! [A_126] : ~ r2_hidden(A_126,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_288,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_270,c_280])).

tff(c_289,plain,(
    ! [A_12] : ~ v1_xboole_0(A_12) ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:08:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.18  
% 2.14/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.18  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > l1_orders_2 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 2.14/1.18  
% 2.14/1.18  %Foreground sorts:
% 2.14/1.18  
% 2.14/1.18  
% 2.14/1.18  %Background operators:
% 2.14/1.18  
% 2.14/1.18  
% 2.14/1.18  %Foreground operators:
% 2.14/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.18  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.14/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.18  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.14/1.18  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 2.14/1.18  tff('#skF_5', type, '#skF_5': $i).
% 2.14/1.18  tff('#skF_6', type, '#skF_6': $i).
% 2.14/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.14/1.18  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 2.14/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.18  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.14/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.14/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.14/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.14/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.14/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.18  
% 2.14/1.19  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.14/1.19  tff(f_58, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.14/1.19  tff(f_113, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 2.14/1.19  tff(f_103, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 2.14/1.19  tff(f_60, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.14/1.19  tff(f_89, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 2.14/1.19  tff(f_62, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.14/1.19  tff(f_75, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.14/1.19  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.14/1.19  tff(c_248, plain, (![A_110, B_111]: (r2_hidden('#skF_1'(A_110, B_111), A_110) | r1_xboole_0(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.14/1.19  tff(c_12, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.14/1.19  tff(c_260, plain, (![A_114, B_115, B_116]: (~r1_xboole_0(A_114, B_115) | r1_xboole_0(k3_xboole_0(A_114, B_115), B_116))), inference(resolution, [status(thm)], [c_248, c_12])).
% 2.14/1.19  tff(c_38, plain, (~r1_lattice3('#skF_5', k1_xboole_0, '#skF_6') | ~r2_lattice3('#skF_5', k1_xboole_0, '#skF_6')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.14/1.19  tff(c_57, plain, (~r2_lattice3('#skF_5', k1_xboole_0, '#skF_6')), inference(splitLeft, [status(thm)], [c_38])).
% 2.14/1.19  tff(c_42, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.14/1.19  tff(c_40, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.14/1.19  tff(c_125, plain, (![A_73, B_74, C_75]: (r2_hidden('#skF_4'(A_73, B_74, C_75), B_74) | r2_lattice3(A_73, B_74, C_75) | ~m1_subset_1(C_75, u1_struct_0(A_73)) | ~l1_orders_2(A_73))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.14/1.19  tff(c_14, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.14/1.19  tff(c_51, plain, (![A_46, B_47, C_48]: (~r1_xboole_0(A_46, B_47) | ~r2_hidden(C_48, k3_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.14/1.19  tff(c_54, plain, (![A_11, C_48]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_48, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_51])).
% 2.14/1.19  tff(c_55, plain, (![C_48]: (~r2_hidden(C_48, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_54])).
% 2.14/1.19  tff(c_136, plain, (![A_76, C_77]: (r2_lattice3(A_76, k1_xboole_0, C_77) | ~m1_subset_1(C_77, u1_struct_0(A_76)) | ~l1_orders_2(A_76))), inference(resolution, [status(thm)], [c_125, c_55])).
% 2.14/1.19  tff(c_139, plain, (r2_lattice3('#skF_5', k1_xboole_0, '#skF_6') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_40, c_136])).
% 2.14/1.19  tff(c_142, plain, (r2_lattice3('#skF_5', k1_xboole_0, '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_139])).
% 2.14/1.19  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_142])).
% 2.14/1.19  tff(c_145, plain, (~r1_lattice3('#skF_5', k1_xboole_0, '#skF_6')), inference(splitRight, [status(thm)], [c_38])).
% 2.14/1.19  tff(c_214, plain, (![A_101, B_102, C_103]: (r2_hidden('#skF_3'(A_101, B_102, C_103), B_102) | r1_lattice3(A_101, B_102, C_103) | ~m1_subset_1(C_103, u1_struct_0(A_101)) | ~l1_orders_2(A_101))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.14/1.19  tff(c_236, plain, (![A_107, C_108]: (r1_lattice3(A_107, k1_xboole_0, C_108) | ~m1_subset_1(C_108, u1_struct_0(A_107)) | ~l1_orders_2(A_107))), inference(resolution, [status(thm)], [c_214, c_55])).
% 2.14/1.19  tff(c_239, plain, (r1_lattice3('#skF_5', k1_xboole_0, '#skF_6') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_40, c_236])).
% 2.14/1.19  tff(c_242, plain, (r1_lattice3('#skF_5', k1_xboole_0, '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_239])).
% 2.14/1.19  tff(c_244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_242])).
% 2.14/1.19  tff(c_245, plain, (![A_11]: (~r1_xboole_0(A_11, k1_xboole_0))), inference(splitRight, [status(thm)], [c_54])).
% 2.14/1.19  tff(c_267, plain, (![A_114, B_115]: (~r1_xboole_0(A_114, B_115))), inference(resolution, [status(thm)], [c_260, c_245])).
% 2.14/1.19  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.14/1.19  tff(c_270, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1))), inference(negUnitSimplification, [status(thm)], [c_267, c_8])).
% 2.14/1.19  tff(c_16, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.14/1.19  tff(c_275, plain, (![C_123, B_124, A_125]: (~v1_xboole_0(C_123) | ~m1_subset_1(B_124, k1_zfmisc_1(C_123)) | ~r2_hidden(A_125, B_124))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.19  tff(c_278, plain, (![A_12, A_125]: (~v1_xboole_0(A_12) | ~r2_hidden(A_125, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_275])).
% 2.14/1.19  tff(c_280, plain, (![A_126]: (~r2_hidden(A_126, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_278])).
% 2.14/1.19  tff(c_288, plain, $false, inference(resolution, [status(thm)], [c_270, c_280])).
% 2.14/1.19  tff(c_289, plain, (![A_12]: (~v1_xboole_0(A_12))), inference(splitRight, [status(thm)], [c_278])).
% 2.14/1.19  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.14/1.19  tff(c_291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_289, c_2])).
% 2.14/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.19  
% 2.14/1.19  Inference rules
% 2.14/1.19  ----------------------
% 2.14/1.19  #Ref     : 0
% 2.14/1.19  #Sup     : 46
% 2.14/1.19  #Fact    : 0
% 2.14/1.19  #Define  : 0
% 2.14/1.19  #Split   : 4
% 2.14/1.19  #Chain   : 0
% 2.14/1.19  #Close   : 0
% 2.14/1.19  
% 2.14/1.19  Ordering : KBO
% 2.14/1.19  
% 2.14/1.19  Simplification rules
% 2.14/1.19  ----------------------
% 2.14/1.19  #Subsume      : 19
% 2.14/1.19  #Demod        : 12
% 2.14/1.19  #Tautology    : 10
% 2.14/1.19  #SimpNegUnit  : 9
% 2.14/1.19  #BackRed      : 3
% 2.14/1.19  
% 2.14/1.19  #Partial instantiations: 0
% 2.14/1.19  #Strategies tried      : 1
% 2.14/1.19  
% 2.14/1.19  Timing (in seconds)
% 2.14/1.19  ----------------------
% 2.14/1.20  Preprocessing        : 0.27
% 2.14/1.20  Parsing              : 0.15
% 2.14/1.20  CNF conversion       : 0.02
% 2.14/1.20  Main loop            : 0.19
% 2.14/1.20  Inferencing          : 0.08
% 2.14/1.20  Reduction            : 0.05
% 2.14/1.20  Demodulation         : 0.03
% 2.14/1.20  BG Simplification    : 0.01
% 2.14/1.20  Subsumption          : 0.03
% 2.14/1.20  Abstraction          : 0.01
% 2.14/1.20  MUC search           : 0.00
% 2.14/1.20  Cooper               : 0.00
% 2.14/1.20  Total                : 0.49
% 2.14/1.20  Index Insertion      : 0.00
% 2.14/1.20  Index Deletion       : 0.00
% 2.14/1.20  Index Matching       : 0.00
% 2.14/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
