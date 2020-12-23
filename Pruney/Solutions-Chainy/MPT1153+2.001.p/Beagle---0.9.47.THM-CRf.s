%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:32 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 111 expanded)
%              Number of leaves         :   25 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  122 ( 440 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

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
                    & r2_hidden(B,k1_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_orders_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_83,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_30,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_24,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_34,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_53,plain,(
    ! [A_37,B_38] :
      ( k1_orders_2(A_37,B_38) = a_2_0_orders_2(A_37,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_orders_2(A_37)
      | ~ v5_orders_2(A_37)
      | ~ v4_orders_2(A_37)
      | ~ v3_orders_2(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_56,plain,
    ( k1_orders_2('#skF_3','#skF_5') = a_2_0_orders_2('#skF_3','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_53])).

tff(c_59,plain,
    ( k1_orders_2('#skF_3','#skF_5') = a_2_0_orders_2('#skF_3','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_56])).

tff(c_60,plain,(
    k1_orders_2('#skF_3','#skF_5') = a_2_0_orders_2('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_59])).

tff(c_22,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_61,plain,(
    r2_hidden('#skF_4',a_2_0_orders_2('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_22])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] :
      ( '#skF_1'(A_11,B_12,C_13) = A_11
      | ~ r2_hidden(A_11,a_2_0_orders_2(B_12,C_13))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(u1_struct_0(B_12)))
      | ~ l1_orders_2(B_12)
      | ~ v5_orders_2(B_12)
      | ~ v4_orders_2(B_12)
      | ~ v3_orders_2(B_12)
      | v2_struct_0(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_68,plain,
    ( '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_18])).

tff(c_71,plain,
    ( '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_26,c_68])).

tff(c_72,plain,(
    '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_71])).

tff(c_131,plain,(
    ! [B_58,E_59,A_60,C_61] :
      ( r2_orders_2(B_58,E_59,'#skF_1'(A_60,B_58,C_61))
      | ~ r2_hidden(E_59,C_61)
      | ~ m1_subset_1(E_59,u1_struct_0(B_58))
      | ~ r2_hidden(A_60,a_2_0_orders_2(B_58,C_61))
      | ~ m1_subset_1(C_61,k1_zfmisc_1(u1_struct_0(B_58)))
      | ~ l1_orders_2(B_58)
      | ~ v5_orders_2(B_58)
      | ~ v4_orders_2(B_58)
      | ~ v3_orders_2(B_58)
      | v2_struct_0(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_133,plain,(
    ! [E_59,A_60] :
      ( r2_orders_2('#skF_3',E_59,'#skF_1'(A_60,'#skF_3','#skF_5'))
      | ~ r2_hidden(E_59,'#skF_5')
      | ~ m1_subset_1(E_59,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_60,a_2_0_orders_2('#skF_3','#skF_5'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_131])).

tff(c_136,plain,(
    ! [E_59,A_60] :
      ( r2_orders_2('#skF_3',E_59,'#skF_1'(A_60,'#skF_3','#skF_5'))
      | ~ r2_hidden(E_59,'#skF_5')
      | ~ m1_subset_1(E_59,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_60,a_2_0_orders_2('#skF_3','#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_133])).

tff(c_138,plain,(
    ! [E_62,A_63] :
      ( r2_orders_2('#skF_3',E_62,'#skF_1'(A_63,'#skF_3','#skF_5'))
      | ~ r2_hidden(E_62,'#skF_5')
      | ~ m1_subset_1(E_62,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_63,a_2_0_orders_2('#skF_3','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_136])).

tff(c_149,plain,(
    ! [E_62] :
      ( r2_orders_2('#skF_3',E_62,'#skF_4')
      | ~ r2_hidden(E_62,'#skF_5')
      | ~ m1_subset_1(E_62,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_4',a_2_0_orders_2('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_138])).

tff(c_162,plain,(
    ! [E_64] :
      ( r2_orders_2('#skF_3',E_64,'#skF_4')
      | ~ r2_hidden(E_64,'#skF_5')
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_149])).

tff(c_173,plain,
    ( r2_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_162])).

tff(c_184,plain,(
    r2_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_173])).

tff(c_4,plain,(
    ! [A_1,C_7] :
      ( ~ r2_orders_2(A_1,C_7,C_7)
      | ~ m1_subset_1(C_7,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_188,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_184,c_4])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:49:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.25  
% 2.31/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.25  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.31/1.25  
% 2.31/1.25  %Foreground sorts:
% 2.31/1.25  
% 2.31/1.25  
% 2.31/1.25  %Background operators:
% 2.31/1.25  
% 2.31/1.25  
% 2.31/1.25  %Foreground operators:
% 2.31/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.31/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.31/1.25  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.31/1.25  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.31/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.25  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 2.31/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.25  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.31/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.31/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.25  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.31/1.25  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.31/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.31/1.25  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.31/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.25  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.31/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.31/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.31/1.25  
% 2.31/1.26  tff(f_106, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_orders_2)).
% 2.31/1.26  tff(f_56, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_orders_2)).
% 2.31/1.26  tff(f_83, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 2.31/1.26  tff(f_40, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 2.31/1.26  tff(c_30, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.31/1.26  tff(c_28, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.31/1.26  tff(c_24, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.31/1.26  tff(c_38, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.31/1.26  tff(c_36, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.31/1.26  tff(c_34, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.31/1.26  tff(c_32, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.31/1.26  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.31/1.26  tff(c_53, plain, (![A_37, B_38]: (k1_orders_2(A_37, B_38)=a_2_0_orders_2(A_37, B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_orders_2(A_37) | ~v5_orders_2(A_37) | ~v4_orders_2(A_37) | ~v3_orders_2(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.31/1.26  tff(c_56, plain, (k1_orders_2('#skF_3', '#skF_5')=a_2_0_orders_2('#skF_3', '#skF_5') | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_26, c_53])).
% 2.31/1.26  tff(c_59, plain, (k1_orders_2('#skF_3', '#skF_5')=a_2_0_orders_2('#skF_3', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_56])).
% 2.31/1.26  tff(c_60, plain, (k1_orders_2('#skF_3', '#skF_5')=a_2_0_orders_2('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_59])).
% 2.31/1.26  tff(c_22, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.31/1.26  tff(c_61, plain, (r2_hidden('#skF_4', a_2_0_orders_2('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_22])).
% 2.31/1.26  tff(c_18, plain, (![A_11, B_12, C_13]: ('#skF_1'(A_11, B_12, C_13)=A_11 | ~r2_hidden(A_11, a_2_0_orders_2(B_12, C_13)) | ~m1_subset_1(C_13, k1_zfmisc_1(u1_struct_0(B_12))) | ~l1_orders_2(B_12) | ~v5_orders_2(B_12) | ~v4_orders_2(B_12) | ~v3_orders_2(B_12) | v2_struct_0(B_12))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.31/1.26  tff(c_68, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_61, c_18])).
% 2.31/1.26  tff(c_71, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_26, c_68])).
% 2.31/1.26  tff(c_72, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_38, c_71])).
% 2.31/1.26  tff(c_131, plain, (![B_58, E_59, A_60, C_61]: (r2_orders_2(B_58, E_59, '#skF_1'(A_60, B_58, C_61)) | ~r2_hidden(E_59, C_61) | ~m1_subset_1(E_59, u1_struct_0(B_58)) | ~r2_hidden(A_60, a_2_0_orders_2(B_58, C_61)) | ~m1_subset_1(C_61, k1_zfmisc_1(u1_struct_0(B_58))) | ~l1_orders_2(B_58) | ~v5_orders_2(B_58) | ~v4_orders_2(B_58) | ~v3_orders_2(B_58) | v2_struct_0(B_58))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.31/1.26  tff(c_133, plain, (![E_59, A_60]: (r2_orders_2('#skF_3', E_59, '#skF_1'(A_60, '#skF_3', '#skF_5')) | ~r2_hidden(E_59, '#skF_5') | ~m1_subset_1(E_59, u1_struct_0('#skF_3')) | ~r2_hidden(A_60, a_2_0_orders_2('#skF_3', '#skF_5')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_131])).
% 2.31/1.26  tff(c_136, plain, (![E_59, A_60]: (r2_orders_2('#skF_3', E_59, '#skF_1'(A_60, '#skF_3', '#skF_5')) | ~r2_hidden(E_59, '#skF_5') | ~m1_subset_1(E_59, u1_struct_0('#skF_3')) | ~r2_hidden(A_60, a_2_0_orders_2('#skF_3', '#skF_5')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_133])).
% 2.31/1.26  tff(c_138, plain, (![E_62, A_63]: (r2_orders_2('#skF_3', E_62, '#skF_1'(A_63, '#skF_3', '#skF_5')) | ~r2_hidden(E_62, '#skF_5') | ~m1_subset_1(E_62, u1_struct_0('#skF_3')) | ~r2_hidden(A_63, a_2_0_orders_2('#skF_3', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_38, c_136])).
% 2.31/1.26  tff(c_149, plain, (![E_62]: (r2_orders_2('#skF_3', E_62, '#skF_4') | ~r2_hidden(E_62, '#skF_5') | ~m1_subset_1(E_62, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_4', a_2_0_orders_2('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_72, c_138])).
% 2.31/1.26  tff(c_162, plain, (![E_64]: (r2_orders_2('#skF_3', E_64, '#skF_4') | ~r2_hidden(E_64, '#skF_5') | ~m1_subset_1(E_64, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_149])).
% 2.31/1.26  tff(c_173, plain, (r2_orders_2('#skF_3', '#skF_4', '#skF_4') | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_28, c_162])).
% 2.31/1.26  tff(c_184, plain, (r2_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_173])).
% 2.31/1.26  tff(c_4, plain, (![A_1, C_7]: (~r2_orders_2(A_1, C_7, C_7) | ~m1_subset_1(C_7, u1_struct_0(A_1)) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.31/1.26  tff(c_188, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_184, c_4])).
% 2.31/1.26  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_188])).
% 2.31/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.26  
% 2.31/1.26  Inference rules
% 2.31/1.26  ----------------------
% 2.31/1.26  #Ref     : 0
% 2.31/1.26  #Sup     : 27
% 2.31/1.26  #Fact    : 0
% 2.31/1.26  #Define  : 0
% 2.31/1.26  #Split   : 0
% 2.31/1.26  #Chain   : 0
% 2.31/1.26  #Close   : 0
% 2.31/1.26  
% 2.31/1.26  Ordering : KBO
% 2.31/1.26  
% 2.31/1.26  Simplification rules
% 2.31/1.26  ----------------------
% 2.31/1.26  #Subsume      : 0
% 2.31/1.26  #Demod        : 59
% 2.31/1.26  #Tautology    : 8
% 2.31/1.26  #SimpNegUnit  : 10
% 2.31/1.26  #BackRed      : 1
% 2.31/1.26  
% 2.31/1.26  #Partial instantiations: 0
% 2.31/1.26  #Strategies tried      : 1
% 2.31/1.26  
% 2.31/1.26  Timing (in seconds)
% 2.31/1.26  ----------------------
% 2.31/1.26  Preprocessing        : 0.31
% 2.31/1.26  Parsing              : 0.16
% 2.31/1.26  CNF conversion       : 0.02
% 2.31/1.26  Main loop            : 0.19
% 2.31/1.26  Inferencing          : 0.07
% 2.31/1.26  Reduction            : 0.06
% 2.31/1.26  Demodulation         : 0.05
% 2.31/1.26  BG Simplification    : 0.02
% 2.31/1.26  Subsumption          : 0.03
% 2.31/1.26  Abstraction          : 0.01
% 2.31/1.26  MUC search           : 0.00
% 2.31/1.26  Cooper               : 0.00
% 2.31/1.26  Total                : 0.53
% 2.31/1.27  Index Insertion      : 0.00
% 2.31/1.27  Index Deletion       : 0.00
% 2.31/1.27  Index Matching       : 0.00
% 2.31/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
