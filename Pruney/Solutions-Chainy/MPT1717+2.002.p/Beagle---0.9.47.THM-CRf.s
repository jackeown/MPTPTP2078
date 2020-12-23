%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:40 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   46 (  72 expanded)
%              Number of leaves         :   22 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  139 ( 242 expanded)
%              Number of equality atoms :   13 (  28 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => k2_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tmap_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( ~ r1_tsep_1(B,C)
               => ( ( m1_pre_topc(B,C)
                   => k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) )
                  & ( k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                   => m1_pre_topc(B,C) )
                  & ( m1_pre_topc(C,B)
                   => k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) )
                  & ( k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
                   => m1_pre_topc(C,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tsep_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( m1_pre_topc(B,C)
               => ( ~ r1_tsep_1(B,C)
                  & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_26,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_36,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_1'(A_30,B_31),A_30)
      | r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_41,plain,(
    ! [A_30] : r1_tarski(A_30,A_30) ),
    inference(resolution,[status(thm)],[c_36,c_4])).

tff(c_60,plain,(
    ! [B_43,C_44,A_45] :
      ( m1_pre_topc(B_43,C_44)
      | ~ r1_tarski(u1_struct_0(B_43),u1_struct_0(C_44))
      | ~ m1_pre_topc(C_44,A_45)
      | ~ m1_pre_topc(B_43,A_45)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_65,plain,(
    ! [B_46,A_47] :
      ( m1_pre_topc(B_46,B_46)
      | ~ m1_pre_topc(B_46,A_47)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_41,c_60])).

tff(c_67,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_65])).

tff(c_70,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_67])).

tff(c_141,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_tsep_1(A_75,B_76,C_77) = g1_pre_topc(u1_struct_0(C_77),u1_pre_topc(C_77))
      | ~ m1_pre_topc(C_77,B_76)
      | r1_tsep_1(B_76,C_77)
      | ~ m1_pre_topc(C_77,A_75)
      | v2_struct_0(C_77)
      | ~ m1_pre_topc(B_76,A_75)
      | v2_struct_0(B_76)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_145,plain,(
    ! [B_76] :
      ( k2_tsep_1('#skF_2',B_76,'#skF_3') = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc('#skF_3',B_76)
      | r1_tsep_1(B_76,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_76,'#skF_2')
      | v2_struct_0(B_76)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_141])).

tff(c_150,plain,(
    ! [B_76] :
      ( k2_tsep_1('#skF_2',B_76,'#skF_3') = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc('#skF_3',B_76)
      | r1_tsep_1(B_76,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_76,'#skF_2')
      | v2_struct_0(B_76)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_145])).

tff(c_152,plain,(
    ! [B_78] :
      ( k2_tsep_1('#skF_2',B_78,'#skF_3') = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc('#skF_3',B_78)
      | r1_tsep_1(B_78,'#skF_3')
      | ~ m1_pre_topc(B_78,'#skF_2')
      | v2_struct_0(B_78) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_28,c_150])).

tff(c_24,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != k2_tsep_1('#skF_2','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_183,plain,(
    ! [B_79] :
      ( k2_tsep_1('#skF_2',B_79,'#skF_3') != k2_tsep_1('#skF_2','#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',B_79)
      | r1_tsep_1(B_79,'#skF_3')
      | ~ m1_pre_topc(B_79,'#skF_2')
      | v2_struct_0(B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_24])).

tff(c_8,plain,(
    ! [C_12,B_10,A_6] :
      ( ~ r1_tsep_1(C_12,B_10)
      | ~ m1_pre_topc(B_10,C_12)
      | ~ m1_pre_topc(C_12,A_6)
      | v2_struct_0(C_12)
      | ~ m1_pre_topc(B_10,A_6)
      | v2_struct_0(B_10)
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_185,plain,(
    ! [B_79,A_6] :
      ( ~ m1_pre_topc(B_79,A_6)
      | ~ m1_pre_topc('#skF_3',A_6)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6)
      | v2_struct_0(A_6)
      | k2_tsep_1('#skF_2',B_79,'#skF_3') != k2_tsep_1('#skF_2','#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',B_79)
      | ~ m1_pre_topc(B_79,'#skF_2')
      | v2_struct_0(B_79) ) ),
    inference(resolution,[status(thm)],[c_183,c_8])).

tff(c_194,plain,(
    ! [B_80,A_81] :
      ( ~ m1_pre_topc(B_80,A_81)
      | ~ m1_pre_topc('#skF_3',A_81)
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81)
      | k2_tsep_1('#skF_2',B_80,'#skF_3') != k2_tsep_1('#skF_2','#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',B_80)
      | ~ m1_pre_topc(B_80,'#skF_2')
      | v2_struct_0(B_80) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_185])).

tff(c_198,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_194])).

tff(c_205,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_70,c_32,c_30,c_198])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_34,c_205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:50:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.53  
% 2.50/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.53  %$ r2_hidden > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1
% 2.50/1.53  
% 2.50/1.53  %Foreground sorts:
% 2.50/1.53  
% 2.50/1.53  
% 2.50/1.53  %Background operators:
% 2.50/1.53  
% 2.50/1.53  
% 2.50/1.53  %Foreground operators:
% 2.50/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.50/1.53  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.50/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.53  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.50/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.50/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.53  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.53  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.53  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.50/1.53  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 2.50/1.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.50/1.53  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.50/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.50/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.50/1.53  
% 2.50/1.55  tff(f_127, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k2_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tmap_1)).
% 2.50/1.55  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.50/1.55  tff(f_111, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.50/1.55  tff(f_97, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => ((((m1_pre_topc(B, C) => (k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))) & ((k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => m1_pre_topc(B, C))) & (m1_pre_topc(C, B) => (k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))))) & ((k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => m1_pre_topc(C, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tsep_1)).
% 2.50/1.55  tff(f_59, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tmap_1)).
% 2.50/1.55  tff(c_28, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.50/1.55  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.50/1.55  tff(c_26, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.50/1.55  tff(c_32, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.50/1.55  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.50/1.55  tff(c_36, plain, (![A_30, B_31]: (r2_hidden('#skF_1'(A_30, B_31), A_30) | r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.50/1.55  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.50/1.55  tff(c_41, plain, (![A_30]: (r1_tarski(A_30, A_30))), inference(resolution, [status(thm)], [c_36, c_4])).
% 2.50/1.55  tff(c_60, plain, (![B_43, C_44, A_45]: (m1_pre_topc(B_43, C_44) | ~r1_tarski(u1_struct_0(B_43), u1_struct_0(C_44)) | ~m1_pre_topc(C_44, A_45) | ~m1_pre_topc(B_43, A_45) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.50/1.55  tff(c_65, plain, (![B_46, A_47]: (m1_pre_topc(B_46, B_46) | ~m1_pre_topc(B_46, A_47) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47))), inference(resolution, [status(thm)], [c_41, c_60])).
% 2.50/1.55  tff(c_67, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_65])).
% 2.50/1.55  tff(c_70, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_67])).
% 2.50/1.55  tff(c_141, plain, (![A_75, B_76, C_77]: (k2_tsep_1(A_75, B_76, C_77)=g1_pre_topc(u1_struct_0(C_77), u1_pre_topc(C_77)) | ~m1_pre_topc(C_77, B_76) | r1_tsep_1(B_76, C_77) | ~m1_pre_topc(C_77, A_75) | v2_struct_0(C_77) | ~m1_pre_topc(B_76, A_75) | v2_struct_0(B_76) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.50/1.55  tff(c_145, plain, (![B_76]: (k2_tsep_1('#skF_2', B_76, '#skF_3')=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc('#skF_3', B_76) | r1_tsep_1(B_76, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_76, '#skF_2') | v2_struct_0(B_76) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_141])).
% 2.50/1.55  tff(c_150, plain, (![B_76]: (k2_tsep_1('#skF_2', B_76, '#skF_3')=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc('#skF_3', B_76) | r1_tsep_1(B_76, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_76, '#skF_2') | v2_struct_0(B_76) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_145])).
% 2.50/1.55  tff(c_152, plain, (![B_78]: (k2_tsep_1('#skF_2', B_78, '#skF_3')=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc('#skF_3', B_78) | r1_tsep_1(B_78, '#skF_3') | ~m1_pre_topc(B_78, '#skF_2') | v2_struct_0(B_78))), inference(negUnitSimplification, [status(thm)], [c_34, c_28, c_150])).
% 2.50/1.55  tff(c_24, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=k2_tsep_1('#skF_2', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.50/1.55  tff(c_183, plain, (![B_79]: (k2_tsep_1('#skF_2', B_79, '#skF_3')!=k2_tsep_1('#skF_2', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', B_79) | r1_tsep_1(B_79, '#skF_3') | ~m1_pre_topc(B_79, '#skF_2') | v2_struct_0(B_79))), inference(superposition, [status(thm), theory('equality')], [c_152, c_24])).
% 2.50/1.55  tff(c_8, plain, (![C_12, B_10, A_6]: (~r1_tsep_1(C_12, B_10) | ~m1_pre_topc(B_10, C_12) | ~m1_pre_topc(C_12, A_6) | v2_struct_0(C_12) | ~m1_pre_topc(B_10, A_6) | v2_struct_0(B_10) | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.50/1.55  tff(c_185, plain, (![B_79, A_6]: (~m1_pre_topc(B_79, A_6) | ~m1_pre_topc('#skF_3', A_6) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6) | v2_struct_0(A_6) | k2_tsep_1('#skF_2', B_79, '#skF_3')!=k2_tsep_1('#skF_2', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', B_79) | ~m1_pre_topc(B_79, '#skF_2') | v2_struct_0(B_79))), inference(resolution, [status(thm)], [c_183, c_8])).
% 2.50/1.55  tff(c_194, plain, (![B_80, A_81]: (~m1_pre_topc(B_80, A_81) | ~m1_pre_topc('#skF_3', A_81) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81) | k2_tsep_1('#skF_2', B_80, '#skF_3')!=k2_tsep_1('#skF_2', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', B_80) | ~m1_pre_topc(B_80, '#skF_2') | v2_struct_0(B_80))), inference(negUnitSimplification, [status(thm)], [c_28, c_185])).
% 2.50/1.55  tff(c_198, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_26, c_194])).
% 2.50/1.55  tff(c_205, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_70, c_32, c_30, c_198])).
% 2.50/1.55  tff(c_207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_34, c_205])).
% 2.50/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.55  
% 2.50/1.55  Inference rules
% 2.50/1.55  ----------------------
% 2.50/1.55  #Ref     : 0
% 2.50/1.55  #Sup     : 37
% 2.50/1.55  #Fact    : 0
% 2.50/1.55  #Define  : 0
% 2.50/1.55  #Split   : 1
% 2.50/1.55  #Chain   : 0
% 2.50/1.55  #Close   : 0
% 2.50/1.55  
% 2.50/1.55  Ordering : KBO
% 2.50/1.55  
% 2.50/1.55  Simplification rules
% 2.50/1.55  ----------------------
% 2.50/1.55  #Subsume      : 9
% 2.50/1.55  #Demod        : 20
% 2.50/1.55  #Tautology    : 6
% 2.50/1.55  #SimpNegUnit  : 10
% 2.50/1.55  #BackRed      : 0
% 2.50/1.55  
% 2.50/1.55  #Partial instantiations: 0
% 2.50/1.55  #Strategies tried      : 1
% 2.50/1.55  
% 2.50/1.55  Timing (in seconds)
% 2.50/1.55  ----------------------
% 2.50/1.55  Preprocessing        : 0.41
% 2.50/1.55  Parsing              : 0.22
% 2.50/1.55  CNF conversion       : 0.03
% 2.50/1.55  Main loop            : 0.29
% 2.50/1.55  Inferencing          : 0.11
% 2.50/1.55  Reduction            : 0.07
% 2.50/1.55  Demodulation         : 0.05
% 2.50/1.55  BG Simplification    : 0.02
% 2.50/1.55  Subsumption          : 0.08
% 2.50/1.55  Abstraction          : 0.02
% 2.50/1.55  MUC search           : 0.00
% 2.50/1.55  Cooper               : 0.00
% 2.50/1.55  Total                : 0.74
% 2.50/1.55  Index Insertion      : 0.00
% 2.50/1.55  Index Deletion       : 0.00
% 2.50/1.55  Index Matching       : 0.00
% 2.50/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
