%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:26 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 107 expanded)
%              Number of leaves         :   30 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  105 ( 287 expanded)
%              Number of equality atoms :    1 (  11 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_107,negated_conjecture,(
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

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_26,plain,(
    ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_36,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_56,plain,(
    ! [B_52,A_53] :
      ( l1_pre_topc(B_52)
      | ~ m1_pre_topc(B_52,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_59,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_56])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_59])).

tff(c_18,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_62,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_56])).

tff(c_71,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_62])).

tff(c_30,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k1_tarski(A_5),B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_102,plain,(
    ! [B_71,A_72] :
      ( m1_subset_1(u1_struct_0(B_71),k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ m1_pre_topc(B_71,A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_107,plain,(
    ! [B_73,A_74] :
      ( r1_tarski(u1_struct_0(B_73),u1_struct_0(A_74))
      | ~ m1_pre_topc(B_73,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_102,c_14])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [A_78,A_79,B_80] :
      ( r1_tarski(A_78,u1_struct_0(A_79))
      | ~ r1_tarski(A_78,u1_struct_0(B_80))
      | ~ m1_pre_topc(B_80,A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_107,c_2])).

tff(c_128,plain,(
    ! [A_84,A_85,B_86] :
      ( r1_tarski(k1_tarski(A_84),u1_struct_0(A_85))
      | ~ m1_pre_topc(B_86,A_85)
      | ~ l1_pre_topc(A_85)
      | ~ r2_hidden(A_84,u1_struct_0(B_86)) ) ),
    inference(resolution,[status(thm)],[c_8,c_115])).

tff(c_134,plain,(
    ! [A_84] :
      ( r1_tarski(k1_tarski(A_84),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_84,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_30,c_128])).

tff(c_215,plain,(
    ! [A_97] :
      ( r1_tarski(k1_tarski(A_97),u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_97,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_134])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | ~ r1_tarski(k1_tarski(A_5),B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_226,plain,(
    ! [A_98] :
      ( r2_hidden(A_98,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_98,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_215,c_6])).

tff(c_231,plain,(
    ! [A_9] :
      ( r2_hidden(A_9,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_9,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_226])).

tff(c_346,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_22,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_349,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_346,c_22])).

tff(c_352,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_349])).

tff(c_366,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_352])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_366])).

tff(c_373,plain,(
    ! [A_113] :
      ( r2_hidden(A_113,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_113,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_398,plain,(
    ! [A_117] :
      ( m1_subset_1(A_117,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_117,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_373,c_10])).

tff(c_401,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_398])).

tff(c_405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.32  
% 2.63/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.32  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.63/1.32  
% 2.63/1.32  %Foreground sorts:
% 2.63/1.32  
% 2.63/1.32  
% 2.63/1.32  %Background operators:
% 2.63/1.32  
% 2.63/1.32  
% 2.63/1.32  %Foreground operators:
% 2.63/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.63/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.63/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.63/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.63/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.32  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.63/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.63/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.63/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.63/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.32  
% 2.63/1.34  tff(f_107, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: (m1_subset_1(E, u1_struct_0(C)) & (E = D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_tmap_1)).
% 2.63/1.34  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.63/1.34  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.63/1.34  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.63/1.34  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.63/1.34  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.63/1.34  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.63/1.34  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.63/1.34  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.63/1.34  tff(f_41, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.63/1.34  tff(c_26, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.63/1.34  tff(c_28, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.63/1.34  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.63/1.34  tff(c_36, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.63/1.34  tff(c_56, plain, (![B_52, A_53]: (l1_pre_topc(B_52) | ~m1_pre_topc(B_52, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.63/1.34  tff(c_59, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_56])).
% 2.63/1.34  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_59])).
% 2.63/1.34  tff(c_18, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.63/1.34  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.63/1.34  tff(c_12, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | v1_xboole_0(B_10) | ~m1_subset_1(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.63/1.34  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.63/1.34  tff(c_62, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_56])).
% 2.63/1.34  tff(c_71, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_62])).
% 2.63/1.34  tff(c_30, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.63/1.34  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k1_tarski(A_5), B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.63/1.34  tff(c_102, plain, (![B_71, A_72]: (m1_subset_1(u1_struct_0(B_71), k1_zfmisc_1(u1_struct_0(A_72))) | ~m1_pre_topc(B_71, A_72) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.63/1.34  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.63/1.34  tff(c_107, plain, (![B_73, A_74]: (r1_tarski(u1_struct_0(B_73), u1_struct_0(A_74)) | ~m1_pre_topc(B_73, A_74) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_102, c_14])).
% 2.63/1.34  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.63/1.34  tff(c_115, plain, (![A_78, A_79, B_80]: (r1_tarski(A_78, u1_struct_0(A_79)) | ~r1_tarski(A_78, u1_struct_0(B_80)) | ~m1_pre_topc(B_80, A_79) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_107, c_2])).
% 2.63/1.34  tff(c_128, plain, (![A_84, A_85, B_86]: (r1_tarski(k1_tarski(A_84), u1_struct_0(A_85)) | ~m1_pre_topc(B_86, A_85) | ~l1_pre_topc(A_85) | ~r2_hidden(A_84, u1_struct_0(B_86)))), inference(resolution, [status(thm)], [c_8, c_115])).
% 2.63/1.34  tff(c_134, plain, (![A_84]: (r1_tarski(k1_tarski(A_84), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~r2_hidden(A_84, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_30, c_128])).
% 2.63/1.34  tff(c_215, plain, (![A_97]: (r1_tarski(k1_tarski(A_97), u1_struct_0('#skF_3')) | ~r2_hidden(A_97, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_134])).
% 2.63/1.34  tff(c_6, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | ~r1_tarski(k1_tarski(A_5), B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.63/1.34  tff(c_226, plain, (![A_98]: (r2_hidden(A_98, u1_struct_0('#skF_3')) | ~r2_hidden(A_98, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_215, c_6])).
% 2.63/1.34  tff(c_231, plain, (![A_9]: (r2_hidden(A_9, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1(A_9, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_226])).
% 2.63/1.34  tff(c_346, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_231])).
% 2.63/1.34  tff(c_22, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.63/1.34  tff(c_349, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_346, c_22])).
% 2.63/1.34  tff(c_352, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_38, c_349])).
% 2.63/1.34  tff(c_366, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_352])).
% 2.63/1.34  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_366])).
% 2.63/1.34  tff(c_373, plain, (![A_113]: (r2_hidden(A_113, u1_struct_0('#skF_3')) | ~m1_subset_1(A_113, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_231])).
% 2.63/1.34  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.63/1.34  tff(c_398, plain, (![A_117]: (m1_subset_1(A_117, u1_struct_0('#skF_3')) | ~m1_subset_1(A_117, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_373, c_10])).
% 2.63/1.34  tff(c_401, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_398])).
% 2.63/1.34  tff(c_405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_401])).
% 2.63/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.34  
% 2.63/1.34  Inference rules
% 2.63/1.34  ----------------------
% 2.63/1.34  #Ref     : 0
% 2.63/1.34  #Sup     : 83
% 2.63/1.34  #Fact    : 0
% 2.63/1.34  #Define  : 0
% 2.63/1.34  #Split   : 3
% 2.63/1.34  #Chain   : 0
% 2.63/1.34  #Close   : 0
% 2.63/1.34  
% 2.63/1.34  Ordering : KBO
% 2.63/1.34  
% 2.63/1.34  Simplification rules
% 2.63/1.34  ----------------------
% 2.63/1.34  #Subsume      : 17
% 2.63/1.34  #Demod        : 16
% 2.63/1.34  #Tautology    : 7
% 2.63/1.34  #SimpNegUnit  : 3
% 2.63/1.34  #BackRed      : 0
% 2.63/1.34  
% 2.63/1.34  #Partial instantiations: 0
% 2.63/1.34  #Strategies tried      : 1
% 2.63/1.34  
% 2.63/1.34  Timing (in seconds)
% 2.63/1.34  ----------------------
% 2.63/1.34  Preprocessing        : 0.31
% 2.63/1.34  Parsing              : 0.16
% 2.63/1.34  CNF conversion       : 0.02
% 2.63/1.34  Main loop            : 0.27
% 2.63/1.34  Inferencing          : 0.10
% 2.63/1.34  Reduction            : 0.07
% 2.63/1.34  Demodulation         : 0.05
% 2.63/1.34  BG Simplification    : 0.01
% 2.63/1.34  Subsumption          : 0.07
% 2.63/1.34  Abstraction          : 0.01
% 2.63/1.34  MUC search           : 0.00
% 2.63/1.34  Cooper               : 0.00
% 2.63/1.34  Total                : 0.61
% 2.63/1.34  Index Insertion      : 0.00
% 2.63/1.34  Index Deletion       : 0.00
% 2.63/1.34  Index Matching       : 0.00
% 2.63/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
