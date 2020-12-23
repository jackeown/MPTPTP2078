%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:32 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 113 expanded)
%              Number of leaves         :   24 (  56 expanded)
%              Depth                    :   15
%              Number of atoms          :  123 ( 451 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(a_2_0_orders_2,type,(
    a_2_0_orders_2: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r2_hidden(B,C)
                    & r2_hidden(B,k1_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_orders_2)).

tff(f_41,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_0_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,E,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ~ r2_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).

tff(c_26,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_20,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_28,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_36,plain,(
    ! [A_27,B_28] :
      ( k1_orders_2(A_27,B_28) = a_2_0_orders_2(A_27,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_orders_2(A_27)
      | ~ v5_orders_2(A_27)
      | ~ v4_orders_2(A_27)
      | ~ v3_orders_2(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_39,plain,
    ( k1_orders_2('#skF_3','#skF_5') = a_2_0_orders_2('#skF_3','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_36])).

tff(c_42,plain,
    ( k1_orders_2('#skF_3','#skF_5') = a_2_0_orders_2('#skF_3','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_39])).

tff(c_43,plain,(
    k1_orders_2('#skF_3','#skF_5') = a_2_0_orders_2('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_42])).

tff(c_18,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_44,plain,(
    r2_hidden('#skF_4',a_2_0_orders_2('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_18])).

tff(c_49,plain,(
    ! [A_29,B_30,C_31] :
      ( '#skF_1'(A_29,B_30,C_31) = A_29
      | ~ r2_hidden(A_29,a_2_0_orders_2(B_30,C_31))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(B_30)))
      | ~ l1_orders_2(B_30)
      | ~ v5_orders_2(B_30)
      | ~ v4_orders_2(B_30)
      | ~ v3_orders_2(B_30)
      | v2_struct_0(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_51,plain,
    ( '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_49])).

tff(c_54,plain,
    ( '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_22,c_51])).

tff(c_55,plain,(
    '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_54])).

tff(c_77,plain,(
    ! [B_45,E_46,A_47,C_48] :
      ( r2_orders_2(B_45,E_46,'#skF_1'(A_47,B_45,C_48))
      | ~ r2_hidden(E_46,C_48)
      | ~ m1_subset_1(E_46,u1_struct_0(B_45))
      | ~ r2_hidden(A_47,a_2_0_orders_2(B_45,C_48))
      | ~ m1_subset_1(C_48,k1_zfmisc_1(u1_struct_0(B_45)))
      | ~ l1_orders_2(B_45)
      | ~ v5_orders_2(B_45)
      | ~ v4_orders_2(B_45)
      | ~ v3_orders_2(B_45)
      | v2_struct_0(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_79,plain,(
    ! [E_46,A_47] :
      ( r2_orders_2('#skF_3',E_46,'#skF_1'(A_47,'#skF_3','#skF_5'))
      | ~ r2_hidden(E_46,'#skF_5')
      | ~ m1_subset_1(E_46,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_47,a_2_0_orders_2('#skF_3','#skF_5'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_77])).

tff(c_82,plain,(
    ! [E_46,A_47] :
      ( r2_orders_2('#skF_3',E_46,'#skF_1'(A_47,'#skF_3','#skF_5'))
      | ~ r2_hidden(E_46,'#skF_5')
      | ~ m1_subset_1(E_46,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_47,a_2_0_orders_2('#skF_3','#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_79])).

tff(c_84,plain,(
    ! [E_49,A_50] :
      ( r2_orders_2('#skF_3',E_49,'#skF_1'(A_50,'#skF_3','#skF_5'))
      | ~ r2_hidden(E_49,'#skF_5')
      | ~ m1_subset_1(E_49,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_50,a_2_0_orders_2('#skF_3','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_82])).

tff(c_93,plain,(
    ! [E_49] :
      ( r2_orders_2('#skF_3',E_49,'#skF_4')
      | ~ r2_hidden(E_49,'#skF_5')
      | ~ m1_subset_1(E_49,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_4',a_2_0_orders_2('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_84])).

tff(c_103,plain,(
    ! [E_51] :
      ( r2_orders_2('#skF_3',E_51,'#skF_4')
      | ~ r2_hidden(E_51,'#skF_5')
      | ~ m1_subset_1(E_51,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_93])).

tff(c_114,plain,
    ( r2_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_103])).

tff(c_125,plain,(
    r2_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_114])).

tff(c_16,plain,(
    ! [A_17,B_18,C_19] :
      ( ~ r2_orders_2(A_17,B_18,B_18)
      | ~ m1_subset_1(C_19,u1_struct_0(A_17))
      | ~ m1_subset_1(B_18,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_127,plain,(
    ! [C_19] :
      ( ~ m1_subset_1(C_19,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_125,c_16])).

tff(c_130,plain,(
    ! [C_19] : ~ m1_subset_1(C_19,u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_127])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.22  
% 2.15/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.22  %$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.15/1.22  
% 2.15/1.22  %Foreground sorts:
% 2.15/1.22  
% 2.15/1.22  
% 2.15/1.22  %Background operators:
% 2.15/1.22  
% 2.15/1.22  
% 2.15/1.22  %Foreground operators:
% 2.15/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.15/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.15/1.22  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.15/1.22  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.15/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.22  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 2.15/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.22  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.15/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.22  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.15/1.22  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.15/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.22  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.15/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.22  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.15/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.15/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.22  
% 2.32/1.23  tff(f_100, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_orders_2)).
% 2.32/1.23  tff(f_41, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 2.32/1.23  tff(f_68, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 2.32/1.23  tff(f_77, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => ~r2_orders_2(A, B, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_orders_2)).
% 2.32/1.23  tff(c_26, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.23  tff(c_24, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.23  tff(c_20, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.23  tff(c_34, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.23  tff(c_32, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.23  tff(c_30, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.23  tff(c_28, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.23  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.23  tff(c_36, plain, (![A_27, B_28]: (k1_orders_2(A_27, B_28)=a_2_0_orders_2(A_27, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_orders_2(A_27) | ~v5_orders_2(A_27) | ~v4_orders_2(A_27) | ~v3_orders_2(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.32/1.23  tff(c_39, plain, (k1_orders_2('#skF_3', '#skF_5')=a_2_0_orders_2('#skF_3', '#skF_5') | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_36])).
% 2.32/1.23  tff(c_42, plain, (k1_orders_2('#skF_3', '#skF_5')=a_2_0_orders_2('#skF_3', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_39])).
% 2.32/1.23  tff(c_43, plain, (k1_orders_2('#skF_3', '#skF_5')=a_2_0_orders_2('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_34, c_42])).
% 2.32/1.23  tff(c_18, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.23  tff(c_44, plain, (r2_hidden('#skF_4', a_2_0_orders_2('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_18])).
% 2.32/1.23  tff(c_49, plain, (![A_29, B_30, C_31]: ('#skF_1'(A_29, B_30, C_31)=A_29 | ~r2_hidden(A_29, a_2_0_orders_2(B_30, C_31)) | ~m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0(B_30))) | ~l1_orders_2(B_30) | ~v5_orders_2(B_30) | ~v4_orders_2(B_30) | ~v3_orders_2(B_30) | v2_struct_0(B_30))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.32/1.23  tff(c_51, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_49])).
% 2.32/1.23  tff(c_54, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_22, c_51])).
% 2.32/1.23  tff(c_55, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_34, c_54])).
% 2.32/1.23  tff(c_77, plain, (![B_45, E_46, A_47, C_48]: (r2_orders_2(B_45, E_46, '#skF_1'(A_47, B_45, C_48)) | ~r2_hidden(E_46, C_48) | ~m1_subset_1(E_46, u1_struct_0(B_45)) | ~r2_hidden(A_47, a_2_0_orders_2(B_45, C_48)) | ~m1_subset_1(C_48, k1_zfmisc_1(u1_struct_0(B_45))) | ~l1_orders_2(B_45) | ~v5_orders_2(B_45) | ~v4_orders_2(B_45) | ~v3_orders_2(B_45) | v2_struct_0(B_45))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.32/1.23  tff(c_79, plain, (![E_46, A_47]: (r2_orders_2('#skF_3', E_46, '#skF_1'(A_47, '#skF_3', '#skF_5')) | ~r2_hidden(E_46, '#skF_5') | ~m1_subset_1(E_46, u1_struct_0('#skF_3')) | ~r2_hidden(A_47, a_2_0_orders_2('#skF_3', '#skF_5')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_77])).
% 2.32/1.23  tff(c_82, plain, (![E_46, A_47]: (r2_orders_2('#skF_3', E_46, '#skF_1'(A_47, '#skF_3', '#skF_5')) | ~r2_hidden(E_46, '#skF_5') | ~m1_subset_1(E_46, u1_struct_0('#skF_3')) | ~r2_hidden(A_47, a_2_0_orders_2('#skF_3', '#skF_5')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_79])).
% 2.32/1.23  tff(c_84, plain, (![E_49, A_50]: (r2_orders_2('#skF_3', E_49, '#skF_1'(A_50, '#skF_3', '#skF_5')) | ~r2_hidden(E_49, '#skF_5') | ~m1_subset_1(E_49, u1_struct_0('#skF_3')) | ~r2_hidden(A_50, a_2_0_orders_2('#skF_3', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_34, c_82])).
% 2.32/1.23  tff(c_93, plain, (![E_49]: (r2_orders_2('#skF_3', E_49, '#skF_4') | ~r2_hidden(E_49, '#skF_5') | ~m1_subset_1(E_49, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_4', a_2_0_orders_2('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_55, c_84])).
% 2.32/1.23  tff(c_103, plain, (![E_51]: (r2_orders_2('#skF_3', E_51, '#skF_4') | ~r2_hidden(E_51, '#skF_5') | ~m1_subset_1(E_51, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_93])).
% 2.32/1.23  tff(c_114, plain, (r2_orders_2('#skF_3', '#skF_4', '#skF_4') | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_103])).
% 2.32/1.23  tff(c_125, plain, (r2_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_114])).
% 2.32/1.23  tff(c_16, plain, (![A_17, B_18, C_19]: (~r2_orders_2(A_17, B_18, B_18) | ~m1_subset_1(C_19, u1_struct_0(A_17)) | ~m1_subset_1(B_18, u1_struct_0(A_17)) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.32/1.23  tff(c_127, plain, (![C_19]: (~m1_subset_1(C_19, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_125, c_16])).
% 2.32/1.23  tff(c_130, plain, (![C_19]: (~m1_subset_1(C_19, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_127])).
% 2.32/1.23  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_24])).
% 2.32/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.23  
% 2.32/1.23  Inference rules
% 2.32/1.23  ----------------------
% 2.32/1.23  #Ref     : 0
% 2.32/1.23  #Sup     : 16
% 2.32/1.23  #Fact    : 0
% 2.32/1.23  #Define  : 0
% 2.32/1.23  #Split   : 0
% 2.32/1.23  #Chain   : 0
% 2.32/1.23  #Close   : 0
% 2.32/1.23  
% 2.32/1.23  Ordering : KBO
% 2.32/1.23  
% 2.32/1.23  Simplification rules
% 2.32/1.23  ----------------------
% 2.32/1.23  #Subsume      : 3
% 2.32/1.23  #Demod        : 42
% 2.32/1.23  #Tautology    : 5
% 2.32/1.23  #SimpNegUnit  : 9
% 2.32/1.23  #BackRed      : 2
% 2.32/1.23  
% 2.32/1.23  #Partial instantiations: 0
% 2.32/1.23  #Strategies tried      : 1
% 2.32/1.23  
% 2.32/1.23  Timing (in seconds)
% 2.32/1.23  ----------------------
% 2.32/1.24  Preprocessing        : 0.31
% 2.32/1.24  Parsing              : 0.16
% 2.32/1.24  CNF conversion       : 0.02
% 2.32/1.24  Main loop            : 0.16
% 2.32/1.24  Inferencing          : 0.06
% 2.32/1.24  Reduction            : 0.05
% 2.32/1.24  Demodulation         : 0.04
% 2.32/1.24  BG Simplification    : 0.01
% 2.32/1.24  Subsumption          : 0.02
% 2.32/1.24  Abstraction          : 0.01
% 2.32/1.24  MUC search           : 0.00
% 2.32/1.24  Cooper               : 0.00
% 2.32/1.24  Total                : 0.49
% 2.32/1.24  Index Insertion      : 0.00
% 2.32/1.24  Index Deletion       : 0.00
% 2.32/1.24  Index Matching       : 0.00
% 2.32/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
