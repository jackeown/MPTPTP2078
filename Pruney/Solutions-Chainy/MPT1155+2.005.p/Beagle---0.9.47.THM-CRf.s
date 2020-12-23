%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:37 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 194 expanded)
%              Number of leaves         :   24 (  88 expanded)
%              Depth                    :   14
%              Number of atoms          :  127 ( 863 expanded)
%              Number of equality atoms :   10 (  32 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(a_2_1_orders_2,type,(
    a_2_1_orders_2: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

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

tff(f_106,negated_conjecture,(
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
                    & r2_hidden(B,k2_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).

tff(f_41,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_1_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r2_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_orders_2)).

tff(c_28,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_20,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_30,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36,plain,(
    ! [A_31,B_32] :
      ( k2_orders_2(A_31,B_32) = a_2_1_orders_2(A_31,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_orders_2(A_31)
      | ~ v5_orders_2(A_31)
      | ~ v4_orders_2(A_31)
      | ~ v3_orders_2(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_39,plain,
    ( k2_orders_2('#skF_3','#skF_5') = a_2_1_orders_2('#skF_3','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_36])).

tff(c_42,plain,
    ( k2_orders_2('#skF_3','#skF_5') = a_2_1_orders_2('#skF_3','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_39])).

tff(c_43,plain,(
    k2_orders_2('#skF_3','#skF_5') = a_2_1_orders_2('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_42])).

tff(c_18,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44,plain,(
    r2_hidden('#skF_4',a_2_1_orders_2('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_18])).

tff(c_49,plain,(
    ! [A_33,B_34,C_35] :
      ( '#skF_1'(A_33,B_34,C_35) = A_33
      | ~ r2_hidden(A_33,a_2_1_orders_2(B_34,C_35))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(B_34)))
      | ~ l1_orders_2(B_34)
      | ~ v5_orders_2(B_34)
      | ~ v4_orders_2(B_34)
      | ~ v3_orders_2(B_34)
      | v2_struct_0(B_34) ) ),
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
    ! [B_49,A_50,C_51,E_52] :
      ( r2_orders_2(B_49,'#skF_1'(A_50,B_49,C_51),E_52)
      | ~ r2_hidden(E_52,C_51)
      | ~ m1_subset_1(E_52,u1_struct_0(B_49))
      | ~ r2_hidden(A_50,a_2_1_orders_2(B_49,C_51))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(u1_struct_0(B_49)))
      | ~ l1_orders_2(B_49)
      | ~ v5_orders_2(B_49)
      | ~ v4_orders_2(B_49)
      | ~ v3_orders_2(B_49)
      | v2_struct_0(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_79,plain,(
    ! [A_50,E_52] :
      ( r2_orders_2('#skF_3','#skF_1'(A_50,'#skF_3','#skF_5'),E_52)
      | ~ r2_hidden(E_52,'#skF_5')
      | ~ m1_subset_1(E_52,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_50,a_2_1_orders_2('#skF_3','#skF_5'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_77])).

tff(c_82,plain,(
    ! [A_50,E_52] :
      ( r2_orders_2('#skF_3','#skF_1'(A_50,'#skF_3','#skF_5'),E_52)
      | ~ r2_hidden(E_52,'#skF_5')
      | ~ m1_subset_1(E_52,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_50,a_2_1_orders_2('#skF_3','#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_79])).

tff(c_84,plain,(
    ! [A_53,E_54] :
      ( r2_orders_2('#skF_3','#skF_1'(A_53,'#skF_3','#skF_5'),E_54)
      | ~ r2_hidden(E_54,'#skF_5')
      | ~ m1_subset_1(E_54,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_53,a_2_1_orders_2('#skF_3','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_82])).

tff(c_92,plain,(
    ! [E_54] :
      ( r2_orders_2('#skF_3','#skF_4',E_54)
      | ~ r2_hidden(E_54,'#skF_5')
      | ~ m1_subset_1(E_54,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_4',a_2_1_orders_2('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_84])).

tff(c_102,plain,(
    ! [E_55] :
      ( r2_orders_2('#skF_3','#skF_4',E_55)
      | ~ r2_hidden(E_55,'#skF_5')
      | ~ m1_subset_1(E_55,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_92])).

tff(c_113,plain,
    ( r2_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_102])).

tff(c_124,plain,(
    r2_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_113])).

tff(c_16,plain,(
    ! [A_17,C_23,B_21] :
      ( ~ r2_orders_2(A_17,C_23,B_21)
      | ~ r2_orders_2(A_17,B_21,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0(A_17))
      | ~ m1_subset_1(B_21,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | ~ v5_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_126,plain,
    ( ~ r2_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_124,c_16])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_124,c_126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n022.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:27:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.18  
% 1.93/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.18  %$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 1.93/1.18  
% 1.93/1.18  %Foreground sorts:
% 1.93/1.18  
% 1.93/1.18  
% 1.93/1.18  %Background operators:
% 1.93/1.18  
% 1.93/1.18  
% 1.93/1.18  %Foreground operators:
% 1.93/1.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.93/1.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.93/1.18  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 1.93/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.18  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 1.93/1.18  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 1.93/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.93/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.18  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 1.93/1.18  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 1.93/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.18  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.93/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.18  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 1.93/1.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.93/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.18  
% 1.93/1.20  tff(f_106, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_orders_2)).
% 1.93/1.20  tff(f_41, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 1.93/1.20  tff(f_68, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 1.93/1.20  tff(f_83, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_orders_2)).
% 1.93/1.20  tff(c_28, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 1.93/1.20  tff(c_26, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 1.93/1.20  tff(c_24, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 1.93/1.20  tff(c_20, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 1.93/1.20  tff(c_34, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 1.93/1.20  tff(c_32, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 1.93/1.20  tff(c_30, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 1.93/1.20  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 1.93/1.20  tff(c_36, plain, (![A_31, B_32]: (k2_orders_2(A_31, B_32)=a_2_1_orders_2(A_31, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_orders_2(A_31) | ~v5_orders_2(A_31) | ~v4_orders_2(A_31) | ~v3_orders_2(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.93/1.20  tff(c_39, plain, (k2_orders_2('#skF_3', '#skF_5')=a_2_1_orders_2('#skF_3', '#skF_5') | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_36])).
% 1.93/1.20  tff(c_42, plain, (k2_orders_2('#skF_3', '#skF_5')=a_2_1_orders_2('#skF_3', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_39])).
% 1.93/1.20  tff(c_43, plain, (k2_orders_2('#skF_3', '#skF_5')=a_2_1_orders_2('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_34, c_42])).
% 1.93/1.20  tff(c_18, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 1.93/1.20  tff(c_44, plain, (r2_hidden('#skF_4', a_2_1_orders_2('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_18])).
% 1.93/1.20  tff(c_49, plain, (![A_33, B_34, C_35]: ('#skF_1'(A_33, B_34, C_35)=A_33 | ~r2_hidden(A_33, a_2_1_orders_2(B_34, C_35)) | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0(B_34))) | ~l1_orders_2(B_34) | ~v5_orders_2(B_34) | ~v4_orders_2(B_34) | ~v3_orders_2(B_34) | v2_struct_0(B_34))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.93/1.20  tff(c_51, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_49])).
% 1.93/1.20  tff(c_54, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_22, c_51])).
% 1.93/1.20  tff(c_55, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_34, c_54])).
% 1.93/1.20  tff(c_77, plain, (![B_49, A_50, C_51, E_52]: (r2_orders_2(B_49, '#skF_1'(A_50, B_49, C_51), E_52) | ~r2_hidden(E_52, C_51) | ~m1_subset_1(E_52, u1_struct_0(B_49)) | ~r2_hidden(A_50, a_2_1_orders_2(B_49, C_51)) | ~m1_subset_1(C_51, k1_zfmisc_1(u1_struct_0(B_49))) | ~l1_orders_2(B_49) | ~v5_orders_2(B_49) | ~v4_orders_2(B_49) | ~v3_orders_2(B_49) | v2_struct_0(B_49))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.93/1.20  tff(c_79, plain, (![A_50, E_52]: (r2_orders_2('#skF_3', '#skF_1'(A_50, '#skF_3', '#skF_5'), E_52) | ~r2_hidden(E_52, '#skF_5') | ~m1_subset_1(E_52, u1_struct_0('#skF_3')) | ~r2_hidden(A_50, a_2_1_orders_2('#skF_3', '#skF_5')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_77])).
% 1.93/1.20  tff(c_82, plain, (![A_50, E_52]: (r2_orders_2('#skF_3', '#skF_1'(A_50, '#skF_3', '#skF_5'), E_52) | ~r2_hidden(E_52, '#skF_5') | ~m1_subset_1(E_52, u1_struct_0('#skF_3')) | ~r2_hidden(A_50, a_2_1_orders_2('#skF_3', '#skF_5')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_79])).
% 1.93/1.20  tff(c_84, plain, (![A_53, E_54]: (r2_orders_2('#skF_3', '#skF_1'(A_53, '#skF_3', '#skF_5'), E_54) | ~r2_hidden(E_54, '#skF_5') | ~m1_subset_1(E_54, u1_struct_0('#skF_3')) | ~r2_hidden(A_53, a_2_1_orders_2('#skF_3', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_34, c_82])).
% 1.93/1.20  tff(c_92, plain, (![E_54]: (r2_orders_2('#skF_3', '#skF_4', E_54) | ~r2_hidden(E_54, '#skF_5') | ~m1_subset_1(E_54, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_4', a_2_1_orders_2('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_55, c_84])).
% 1.93/1.20  tff(c_102, plain, (![E_55]: (r2_orders_2('#skF_3', '#skF_4', E_55) | ~r2_hidden(E_55, '#skF_5') | ~m1_subset_1(E_55, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_92])).
% 1.93/1.20  tff(c_113, plain, (r2_orders_2('#skF_3', '#skF_4', '#skF_4') | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_102])).
% 1.93/1.20  tff(c_124, plain, (r2_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_113])).
% 1.93/1.20  tff(c_16, plain, (![A_17, C_23, B_21]: (~r2_orders_2(A_17, C_23, B_21) | ~r2_orders_2(A_17, B_21, C_23) | ~m1_subset_1(C_23, u1_struct_0(A_17)) | ~m1_subset_1(B_21, u1_struct_0(A_17)) | ~l1_orders_2(A_17) | ~v5_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.93/1.20  tff(c_126, plain, (~r2_orders_2('#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_124, c_16])).
% 1.93/1.20  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_124, c_126])).
% 1.93/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  Inference rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Ref     : 0
% 1.93/1.20  #Sup     : 16
% 1.93/1.20  #Fact    : 0
% 1.93/1.20  #Define  : 0
% 1.93/1.20  #Split   : 0
% 1.93/1.20  #Chain   : 0
% 1.93/1.20  #Close   : 0
% 1.93/1.20  
% 1.93/1.20  Ordering : KBO
% 1.93/1.20  
% 1.93/1.20  Simplification rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Subsume      : 0
% 1.93/1.20  #Demod        : 45
% 1.93/1.20  #Tautology    : 5
% 1.93/1.20  #SimpNegUnit  : 8
% 1.93/1.20  #BackRed      : 1
% 1.93/1.20  
% 1.93/1.20  #Partial instantiations: 0
% 1.93/1.20  #Strategies tried      : 1
% 1.93/1.20  
% 1.93/1.20  Timing (in seconds)
% 1.93/1.20  ----------------------
% 1.93/1.20  Preprocessing        : 0.30
% 1.93/1.20  Parsing              : 0.15
% 1.93/1.20  CNF conversion       : 0.02
% 1.93/1.20  Main loop            : 0.15
% 1.93/1.20  Inferencing          : 0.06
% 1.93/1.20  Reduction            : 0.05
% 1.93/1.20  Demodulation         : 0.04
% 1.93/1.20  BG Simplification    : 0.01
% 1.93/1.20  Subsumption          : 0.02
% 1.93/1.20  Abstraction          : 0.01
% 1.93/1.20  MUC search           : 0.00
% 1.93/1.20  Cooper               : 0.00
% 1.93/1.20  Total                : 0.47
% 1.93/1.20  Index Insertion      : 0.00
% 1.93/1.20  Index Deletion       : 0.00
% 1.93/1.20  Index Matching       : 0.00
% 1.93/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
