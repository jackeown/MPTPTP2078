%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:25 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   67 (  89 expanded)
%              Number of leaves         :   28 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  127 ( 288 expanded)
%              Number of equality atoms :    2 (  15 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
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
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(B))
                     => ? [E] :
                          ( m1_subset_1(E,u1_struct_0(C))
                          & E = D ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tmap_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_38,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_50,plain,(
    ! [B_54,A_55] :
      ( l1_pre_topc(B_54)
      | ~ m1_pre_topc(B_54,A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_53,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_50])).

tff(c_62,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_53])).

tff(c_18,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_28,plain,(
    ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_32,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_84,plain,(
    ! [B_65,A_66] :
      ( v2_pre_topc(B_65)
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_90,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_84])).

tff(c_99,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_90])).

tff(c_56,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_50])).

tff(c_65,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_56])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_187,plain,(
    ! [B_83,C_84,A_85] :
      ( m1_pre_topc(B_83,C_84)
      | ~ r1_tarski(u1_struct_0(B_83),u1_struct_0(C_84))
      | ~ m1_pre_topc(C_84,A_85)
      | ~ m1_pre_topc(B_83,A_85)
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_201,plain,(
    ! [B_86,A_87] :
      ( m1_pre_topc(B_86,B_86)
      | ~ m1_pre_topc(B_86,A_87)
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_6,c_187])).

tff(c_205,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_201])).

tff(c_213,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_205])).

tff(c_24,plain,(
    ! [B_22,C_24,A_18] :
      ( r1_tarski(u1_struct_0(B_22),u1_struct_0(C_24))
      | ~ m1_pre_topc(B_22,C_24)
      | ~ m1_pre_topc(C_24,A_18)
      | ~ m1_pre_topc(B_22,A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_243,plain,(
    ! [B_22] :
      ( r1_tarski(u1_struct_0(B_22),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_22,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_213,c_24])).

tff(c_280,plain,(
    ! [B_89] :
      ( r1_tarski(u1_struct_0(B_89),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_89,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_65,c_243])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_105,plain,(
    ! [A_67,C_68,B_69] :
      ( m1_subset_1(A_67,C_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_109,plain,(
    ! [A_70,B_71,A_72] :
      ( m1_subset_1(A_70,B_71)
      | ~ r2_hidden(A_70,A_72)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(resolution,[status(thm)],[c_12,c_105])).

tff(c_112,plain,(
    ! [A_3,B_71,B_4] :
      ( m1_subset_1(A_3,B_71)
      | ~ r1_tarski(B_4,B_71)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_109])).

tff(c_345,plain,(
    ! [A_92,B_93] :
      ( m1_subset_1(A_92,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0(B_93))
      | ~ m1_subset_1(A_92,u1_struct_0(B_93))
      | ~ m1_pre_topc(B_93,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_280,c_112])).

tff(c_347,plain,
    ( m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_345])).

tff(c_350,plain,
    ( m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_347])).

tff(c_351,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_350])).

tff(c_22,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_354,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_351,c_22])).

tff(c_357,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_354])).

tff(c_360,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_357])).

tff(c_364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:31:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.40  
% 2.14/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.40  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.14/1.40  
% 2.14/1.40  %Foreground sorts:
% 2.14/1.40  
% 2.14/1.40  
% 2.14/1.40  %Background operators:
% 2.14/1.40  
% 2.14/1.40  
% 2.14/1.40  %Foreground operators:
% 2.14/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.14/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.14/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.14/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.14/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.14/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.14/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.40  
% 2.14/1.41  tff(f_119, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: (m1_subset_1(E, u1_struct_0(C)) & (E = D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_tmap_1)).
% 2.14/1.41  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.14/1.41  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.14/1.41  tff(f_56, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.14/1.41  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.14/1.41  tff(f_89, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.14/1.41  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.14/1.41  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.14/1.41  tff(f_47, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.14/1.41  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.14/1.41  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.14/1.41  tff(c_38, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.14/1.41  tff(c_50, plain, (![B_54, A_55]: (l1_pre_topc(B_54) | ~m1_pre_topc(B_54, A_55) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.14/1.41  tff(c_53, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_50])).
% 2.14/1.41  tff(c_62, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_53])).
% 2.14/1.41  tff(c_18, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.14/1.41  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.14/1.41  tff(c_28, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.14/1.41  tff(c_32, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.14/1.41  tff(c_30, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.14/1.41  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.14/1.41  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.14/1.41  tff(c_84, plain, (![B_65, A_66]: (v2_pre_topc(B_65) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.14/1.41  tff(c_90, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_84])).
% 2.14/1.41  tff(c_99, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_90])).
% 2.14/1.41  tff(c_56, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_50])).
% 2.14/1.41  tff(c_65, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_56])).
% 2.14/1.41  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.41  tff(c_187, plain, (![B_83, C_84, A_85]: (m1_pre_topc(B_83, C_84) | ~r1_tarski(u1_struct_0(B_83), u1_struct_0(C_84)) | ~m1_pre_topc(C_84, A_85) | ~m1_pre_topc(B_83, A_85) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.14/1.41  tff(c_201, plain, (![B_86, A_87]: (m1_pre_topc(B_86, B_86) | ~m1_pre_topc(B_86, A_87) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87))), inference(resolution, [status(thm)], [c_6, c_187])).
% 2.14/1.41  tff(c_205, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_201])).
% 2.14/1.41  tff(c_213, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_205])).
% 2.14/1.41  tff(c_24, plain, (![B_22, C_24, A_18]: (r1_tarski(u1_struct_0(B_22), u1_struct_0(C_24)) | ~m1_pre_topc(B_22, C_24) | ~m1_pre_topc(C_24, A_18) | ~m1_pre_topc(B_22, A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.14/1.41  tff(c_243, plain, (![B_22]: (r1_tarski(u1_struct_0(B_22), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_22, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_213, c_24])).
% 2.14/1.41  tff(c_280, plain, (![B_89]: (r1_tarski(u1_struct_0(B_89), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_89, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_65, c_243])).
% 2.14/1.41  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.14/1.41  tff(c_12, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.14/1.41  tff(c_105, plain, (![A_67, C_68, B_69]: (m1_subset_1(A_67, C_68) | ~m1_subset_1(B_69, k1_zfmisc_1(C_68)) | ~r2_hidden(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.14/1.41  tff(c_109, plain, (![A_70, B_71, A_72]: (m1_subset_1(A_70, B_71) | ~r2_hidden(A_70, A_72) | ~r1_tarski(A_72, B_71))), inference(resolution, [status(thm)], [c_12, c_105])).
% 2.14/1.41  tff(c_112, plain, (![A_3, B_71, B_4]: (m1_subset_1(A_3, B_71) | ~r1_tarski(B_4, B_71) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_109])).
% 2.14/1.41  tff(c_345, plain, (![A_92, B_93]: (m1_subset_1(A_92, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0(B_93)) | ~m1_subset_1(A_92, u1_struct_0(B_93)) | ~m1_pre_topc(B_93, '#skF_3'))), inference(resolution, [status(thm)], [c_280, c_112])).
% 2.14/1.41  tff(c_347, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_345])).
% 2.14/1.41  tff(c_350, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_347])).
% 2.14/1.41  tff(c_351, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_28, c_350])).
% 2.14/1.41  tff(c_22, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.41  tff(c_354, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_351, c_22])).
% 2.14/1.41  tff(c_357, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_354])).
% 2.14/1.41  tff(c_360, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_357])).
% 2.14/1.41  tff(c_364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_360])).
% 2.14/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.41  
% 2.14/1.41  Inference rules
% 2.14/1.41  ----------------------
% 2.14/1.41  #Ref     : 0
% 2.14/1.41  #Sup     : 56
% 2.14/1.41  #Fact    : 0
% 2.14/1.41  #Define  : 0
% 2.14/1.41  #Split   : 1
% 2.14/1.41  #Chain   : 0
% 2.14/1.41  #Close   : 0
% 2.14/1.41  
% 2.14/1.41  Ordering : KBO
% 2.14/1.41  
% 2.14/1.41  Simplification rules
% 2.14/1.41  ----------------------
% 2.14/1.41  #Subsume      : 8
% 2.14/1.41  #Demod        : 65
% 2.14/1.41  #Tautology    : 26
% 2.14/1.41  #SimpNegUnit  : 2
% 2.14/1.41  #BackRed      : 0
% 2.14/1.41  
% 2.14/1.41  #Partial instantiations: 0
% 2.14/1.41  #Strategies tried      : 1
% 2.14/1.41  
% 2.14/1.41  Timing (in seconds)
% 2.14/1.41  ----------------------
% 2.14/1.42  Preprocessing        : 0.28
% 2.14/1.42  Parsing              : 0.15
% 2.14/1.42  CNF conversion       : 0.02
% 2.14/1.42  Main loop            : 0.23
% 2.14/1.42  Inferencing          : 0.09
% 2.14/1.42  Reduction            : 0.07
% 2.14/1.42  Demodulation         : 0.05
% 2.14/1.42  BG Simplification    : 0.02
% 2.14/1.42  Subsumption          : 0.04
% 2.14/1.42  Abstraction          : 0.01
% 2.14/1.42  MUC search           : 0.00
% 2.14/1.42  Cooper               : 0.00
% 2.14/1.42  Total                : 0.54
% 2.14/1.42  Index Insertion      : 0.00
% 2.14/1.42  Index Deletion       : 0.00
% 2.14/1.42  Index Matching       : 0.00
% 2.14/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
