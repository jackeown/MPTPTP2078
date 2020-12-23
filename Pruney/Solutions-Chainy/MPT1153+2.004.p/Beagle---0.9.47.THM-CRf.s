%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:32 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 126 expanded)
%              Number of leaves         :   26 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  144 ( 512 expanded)
%              Number of equality atoms :   10 (  16 expanded)
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

tff(f_118,negated_conjecture,(
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

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r1_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).

tff(c_30,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_28,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_37,plain,(
    ! [A_31,B_32] :
      ( r1_orders_2(A_31,B_32,B_32)
      | ~ m1_subset_1(B_32,u1_struct_0(A_31))
      | ~ l1_orders_2(A_31)
      | ~ v3_orders_2(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_39,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_37])).

tff(c_42,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_39])).

tff(c_43,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_42])).

tff(c_22,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_32,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_45,plain,(
    ! [A_36,B_37] :
      ( k1_orders_2(A_36,B_37) = a_2_0_orders_2(A_36,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_orders_2(A_36)
      | ~ v5_orders_2(A_36)
      | ~ v4_orders_2(A_36)
      | ~ v3_orders_2(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,
    ( k1_orders_2('#skF_3','#skF_5') = a_2_0_orders_2('#skF_3','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_45])).

tff(c_51,plain,
    ( k1_orders_2('#skF_3','#skF_5') = a_2_0_orders_2('#skF_3','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_48])).

tff(c_52,plain,(
    k1_orders_2('#skF_3','#skF_5') = a_2_0_orders_2('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_51])).

tff(c_20,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_53,plain,(
    r2_hidden('#skF_4',a_2_0_orders_2('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_20])).

tff(c_58,plain,(
    ! [A_38,B_39,C_40] :
      ( '#skF_1'(A_38,B_39,C_40) = A_38
      | ~ r2_hidden(A_38,a_2_0_orders_2(B_39,C_40))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(u1_struct_0(B_39)))
      | ~ l1_orders_2(B_39)
      | ~ v5_orders_2(B_39)
      | ~ v4_orders_2(B_39)
      | ~ v3_orders_2(B_39)
      | v2_struct_0(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_60,plain,
    ( '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_58])).

tff(c_63,plain,
    ( '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_24,c_60])).

tff(c_64,plain,(
    '#skF_1'('#skF_4','#skF_3','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_63])).

tff(c_105,plain,(
    ! [B_57,E_58,A_59,C_60] :
      ( r2_orders_2(B_57,E_58,'#skF_1'(A_59,B_57,C_60))
      | ~ r2_hidden(E_58,C_60)
      | ~ m1_subset_1(E_58,u1_struct_0(B_57))
      | ~ r2_hidden(A_59,a_2_0_orders_2(B_57,C_60))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0(B_57)))
      | ~ l1_orders_2(B_57)
      | ~ v5_orders_2(B_57)
      | ~ v4_orders_2(B_57)
      | ~ v3_orders_2(B_57)
      | v2_struct_0(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_107,plain,(
    ! [E_58,A_59] :
      ( r2_orders_2('#skF_3',E_58,'#skF_1'(A_59,'#skF_3','#skF_5'))
      | ~ r2_hidden(E_58,'#skF_5')
      | ~ m1_subset_1(E_58,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_59,a_2_0_orders_2('#skF_3','#skF_5'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_105])).

tff(c_110,plain,(
    ! [E_58,A_59] :
      ( r2_orders_2('#skF_3',E_58,'#skF_1'(A_59,'#skF_3','#skF_5'))
      | ~ r2_hidden(E_58,'#skF_5')
      | ~ m1_subset_1(E_58,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_59,a_2_0_orders_2('#skF_3','#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_107])).

tff(c_112,plain,(
    ! [E_61,A_62] :
      ( r2_orders_2('#skF_3',E_61,'#skF_1'(A_62,'#skF_3','#skF_5'))
      | ~ r2_hidden(E_61,'#skF_5')
      | ~ m1_subset_1(E_61,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_62,a_2_0_orders_2('#skF_3','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_110])).

tff(c_120,plain,(
    ! [E_61] :
      ( r2_orders_2('#skF_3',E_61,'#skF_4')
      | ~ r2_hidden(E_61,'#skF_5')
      | ~ m1_subset_1(E_61,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_4',a_2_0_orders_2('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_112])).

tff(c_131,plain,(
    ! [E_66] :
      ( r2_orders_2('#skF_3',E_66,'#skF_4')
      | ~ r2_hidden(E_66,'#skF_5')
      | ~ m1_subset_1(E_66,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_120])).

tff(c_142,plain,
    ( r2_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_131])).

tff(c_153,plain,(
    r2_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_142])).

tff(c_18,plain,(
    ! [A_20,C_26,B_24] :
      ( ~ r2_orders_2(A_20,C_26,B_24)
      | ~ r1_orders_2(A_20,B_24,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_20))
      | ~ m1_subset_1(B_24,u1_struct_0(A_20))
      | ~ l1_orders_2(A_20)
      | ~ v5_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_155,plain,
    ( ~ r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_153,c_18])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_43,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:43:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.25  
% 2.35/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.25  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.35/1.25  
% 2.35/1.25  %Foreground sorts:
% 2.35/1.25  
% 2.35/1.25  
% 2.35/1.25  %Background operators:
% 2.35/1.25  
% 2.35/1.25  
% 2.35/1.25  %Foreground operators:
% 2.35/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.35/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.35/1.25  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.35/1.25  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.35/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.25  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 2.35/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.25  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.35/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.35/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.35/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.25  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.35/1.25  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.35/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.25  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.35/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.35/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.25  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.35/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.35/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.25  
% 2.35/1.26  tff(f_118, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_orders_2)).
% 2.35/1.26  tff(f_80, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 2.35/1.26  tff(f_41, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_orders_2)).
% 2.35/1.26  tff(f_68, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 2.35/1.26  tff(f_95, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_orders_2)).
% 2.35/1.26  tff(c_30, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.35/1.26  tff(c_28, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.35/1.26  tff(c_26, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.35/1.26  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.35/1.26  tff(c_34, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.35/1.26  tff(c_37, plain, (![A_31, B_32]: (r1_orders_2(A_31, B_32, B_32) | ~m1_subset_1(B_32, u1_struct_0(A_31)) | ~l1_orders_2(A_31) | ~v3_orders_2(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.35/1.26  tff(c_39, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_26, c_37])).
% 2.35/1.26  tff(c_42, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_39])).
% 2.35/1.26  tff(c_43, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_36, c_42])).
% 2.35/1.26  tff(c_22, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.35/1.26  tff(c_32, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.35/1.26  tff(c_24, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.35/1.26  tff(c_45, plain, (![A_36, B_37]: (k1_orders_2(A_36, B_37)=a_2_0_orders_2(A_36, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_orders_2(A_36) | ~v5_orders_2(A_36) | ~v4_orders_2(A_36) | ~v3_orders_2(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.35/1.26  tff(c_48, plain, (k1_orders_2('#skF_3', '#skF_5')=a_2_0_orders_2('#skF_3', '#skF_5') | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_45])).
% 2.35/1.26  tff(c_51, plain, (k1_orders_2('#skF_3', '#skF_5')=a_2_0_orders_2('#skF_3', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_48])).
% 2.35/1.26  tff(c_52, plain, (k1_orders_2('#skF_3', '#skF_5')=a_2_0_orders_2('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_36, c_51])).
% 2.35/1.26  tff(c_20, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.35/1.26  tff(c_53, plain, (r2_hidden('#skF_4', a_2_0_orders_2('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_20])).
% 2.35/1.26  tff(c_58, plain, (![A_38, B_39, C_40]: ('#skF_1'(A_38, B_39, C_40)=A_38 | ~r2_hidden(A_38, a_2_0_orders_2(B_39, C_40)) | ~m1_subset_1(C_40, k1_zfmisc_1(u1_struct_0(B_39))) | ~l1_orders_2(B_39) | ~v5_orders_2(B_39) | ~v4_orders_2(B_39) | ~v3_orders_2(B_39) | v2_struct_0(B_39))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.35/1.26  tff(c_60, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_53, c_58])).
% 2.35/1.26  tff(c_63, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_24, c_60])).
% 2.35/1.26  tff(c_64, plain, ('#skF_1'('#skF_4', '#skF_3', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_36, c_63])).
% 2.35/1.26  tff(c_105, plain, (![B_57, E_58, A_59, C_60]: (r2_orders_2(B_57, E_58, '#skF_1'(A_59, B_57, C_60)) | ~r2_hidden(E_58, C_60) | ~m1_subset_1(E_58, u1_struct_0(B_57)) | ~r2_hidden(A_59, a_2_0_orders_2(B_57, C_60)) | ~m1_subset_1(C_60, k1_zfmisc_1(u1_struct_0(B_57))) | ~l1_orders_2(B_57) | ~v5_orders_2(B_57) | ~v4_orders_2(B_57) | ~v3_orders_2(B_57) | v2_struct_0(B_57))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.35/1.26  tff(c_107, plain, (![E_58, A_59]: (r2_orders_2('#skF_3', E_58, '#skF_1'(A_59, '#skF_3', '#skF_5')) | ~r2_hidden(E_58, '#skF_5') | ~m1_subset_1(E_58, u1_struct_0('#skF_3')) | ~r2_hidden(A_59, a_2_0_orders_2('#skF_3', '#skF_5')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_105])).
% 2.35/1.26  tff(c_110, plain, (![E_58, A_59]: (r2_orders_2('#skF_3', E_58, '#skF_1'(A_59, '#skF_3', '#skF_5')) | ~r2_hidden(E_58, '#skF_5') | ~m1_subset_1(E_58, u1_struct_0('#skF_3')) | ~r2_hidden(A_59, a_2_0_orders_2('#skF_3', '#skF_5')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_107])).
% 2.35/1.26  tff(c_112, plain, (![E_61, A_62]: (r2_orders_2('#skF_3', E_61, '#skF_1'(A_62, '#skF_3', '#skF_5')) | ~r2_hidden(E_61, '#skF_5') | ~m1_subset_1(E_61, u1_struct_0('#skF_3')) | ~r2_hidden(A_62, a_2_0_orders_2('#skF_3', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_36, c_110])).
% 2.35/1.26  tff(c_120, plain, (![E_61]: (r2_orders_2('#skF_3', E_61, '#skF_4') | ~r2_hidden(E_61, '#skF_5') | ~m1_subset_1(E_61, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_4', a_2_0_orders_2('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_112])).
% 2.35/1.26  tff(c_131, plain, (![E_66]: (r2_orders_2('#skF_3', E_66, '#skF_4') | ~r2_hidden(E_66, '#skF_5') | ~m1_subset_1(E_66, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_120])).
% 2.35/1.26  tff(c_142, plain, (r2_orders_2('#skF_3', '#skF_4', '#skF_4') | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_26, c_131])).
% 2.35/1.26  tff(c_153, plain, (r2_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_142])).
% 2.35/1.26  tff(c_18, plain, (![A_20, C_26, B_24]: (~r2_orders_2(A_20, C_26, B_24) | ~r1_orders_2(A_20, B_24, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_20)) | ~m1_subset_1(B_24, u1_struct_0(A_20)) | ~l1_orders_2(A_20) | ~v5_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.35/1.26  tff(c_155, plain, (~r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_153, c_18])).
% 2.35/1.26  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_43, c_155])).
% 2.35/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.26  
% 2.35/1.26  Inference rules
% 2.35/1.26  ----------------------
% 2.35/1.26  #Ref     : 0
% 2.35/1.26  #Sup     : 21
% 2.35/1.26  #Fact    : 0
% 2.35/1.26  #Define  : 0
% 2.35/1.26  #Split   : 0
% 2.35/1.26  #Chain   : 0
% 2.35/1.26  #Close   : 0
% 2.35/1.26  
% 2.35/1.26  Ordering : KBO
% 2.35/1.26  
% 2.35/1.26  Simplification rules
% 2.35/1.26  ----------------------
% 2.35/1.26  #Subsume      : 0
% 2.35/1.26  #Demod        : 63
% 2.35/1.26  #Tautology    : 7
% 2.35/1.26  #SimpNegUnit  : 11
% 2.35/1.26  #BackRed      : 1
% 2.35/1.26  
% 2.35/1.26  #Partial instantiations: 0
% 2.35/1.26  #Strategies tried      : 1
% 2.35/1.26  
% 2.35/1.26  Timing (in seconds)
% 2.35/1.26  ----------------------
% 2.35/1.27  Preprocessing        : 0.31
% 2.35/1.27  Parsing              : 0.16
% 2.35/1.27  CNF conversion       : 0.02
% 2.35/1.27  Main loop            : 0.17
% 2.35/1.27  Inferencing          : 0.07
% 2.35/1.27  Reduction            : 0.06
% 2.35/1.27  Demodulation         : 0.04
% 2.35/1.27  BG Simplification    : 0.01
% 2.35/1.27  Subsumption          : 0.03
% 2.35/1.27  Abstraction          : 0.01
% 2.35/1.27  MUC search           : 0.00
% 2.35/1.27  Cooper               : 0.00
% 2.35/1.27  Total                : 0.52
% 2.35/1.27  Index Insertion      : 0.00
% 2.35/1.27  Index Deletion       : 0.00
% 2.35/1.27  Index Matching       : 0.00
% 2.35/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
