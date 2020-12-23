%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:40 EST 2020

% Result     : Theorem 14.65s
% Output     : CNFRefutation 14.65s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 109 expanded)
%              Number of leaves         :   33 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :  149 ( 336 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ r2_hidden(B,k2_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_123,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ~ ( ? [D] :
                        ( v6_orders_2(D,A)
                        & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(B,D)
                        & r2_hidden(C,D) )
                    & ~ r1_orders_2(A,B,C)
                    & ~ r1_orders_2(A,C,B) )
                & ~ ( ( r1_orders_2(A,B,C)
                      | r1_orders_2(A,C,B) )
                    & ! [D] :
                        ( ( v6_orders_2(D,A)
                          & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                       => ~ ( r2_hidden(B,D)
                            & r2_hidden(C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_orders_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_145,axiom,(
    ! [A] :
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

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_64,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_62,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_60,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_58,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_107,plain,(
    ! [A_66,B_67] :
      ( k6_domain_1(A_66,B_67) = k1_tarski(B_67)
      | ~ m1_subset_1(B_67,A_66)
      | v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_111,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_107])).

tff(c_113,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_114,plain,(
    ! [A_71,B_72] :
      ( r1_orders_2(A_71,B_72,B_72)
      | ~ m1_subset_1(B_72,u1_struct_0(A_71))
      | ~ l1_orders_2(A_71)
      | ~ v3_orders_2(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_116,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_5')
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_114])).

tff(c_119,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_116])).

tff(c_120,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_119])).

tff(c_40,plain,(
    ! [A_22,C_40,B_34] :
      ( ~ r1_orders_2(A_22,C_40,B_34)
      | r2_hidden(B_34,'#skF_3'(A_22,B_34,C_40))
      | ~ m1_subset_1(C_40,u1_struct_0(A_22))
      | ~ m1_subset_1(B_34,u1_struct_0(A_22))
      | ~ l1_orders_2(A_22)
      | ~ v3_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3434,plain,(
    ! [A_3559,C_3560,B_3561] :
      ( ~ r1_orders_2(A_3559,C_3560,B_3561)
      | m1_subset_1('#skF_3'(A_3559,B_3561,C_3560),k1_zfmisc_1(u1_struct_0(A_3559)))
      | ~ m1_subset_1(C_3560,u1_struct_0(A_3559))
      | ~ m1_subset_1(B_3561,u1_struct_0(A_3559))
      | ~ l1_orders_2(A_3559)
      | ~ v3_orders_2(A_3559) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_24,plain,(
    ! [C_13,B_12,A_11] :
      ( ~ v1_xboole_0(C_13)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(C_13))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34954,plain,(
    ! [A_11094,A_11095,B_11096,C_11097] :
      ( ~ v1_xboole_0(u1_struct_0(A_11094))
      | ~ r2_hidden(A_11095,'#skF_3'(A_11094,B_11096,C_11097))
      | ~ r1_orders_2(A_11094,C_11097,B_11096)
      | ~ m1_subset_1(C_11097,u1_struct_0(A_11094))
      | ~ m1_subset_1(B_11096,u1_struct_0(A_11094))
      | ~ l1_orders_2(A_11094)
      | ~ v3_orders_2(A_11094) ) ),
    inference(resolution,[status(thm)],[c_3434,c_24])).

tff(c_34996,plain,(
    ! [A_11224,C_11225,B_11226] :
      ( ~ v1_xboole_0(u1_struct_0(A_11224))
      | ~ r1_orders_2(A_11224,C_11225,B_11226)
      | ~ m1_subset_1(C_11225,u1_struct_0(A_11224))
      | ~ m1_subset_1(B_11226,u1_struct_0(A_11224))
      | ~ l1_orders_2(A_11224)
      | ~ v3_orders_2(A_11224) ) ),
    inference(resolution,[status(thm)],[c_40,c_34954])).

tff(c_34998,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_34996])).

tff(c_35002,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_56,c_113,c_34998])).

tff(c_35003,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_35027,plain,(
    ! [A_11366,B_11367] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_11366),B_11367),k1_zfmisc_1(u1_struct_0(A_11366)))
      | ~ m1_subset_1(B_11367,u1_struct_0(A_11366))
      | ~ l1_orders_2(A_11366)
      | ~ v3_orders_2(A_11366)
      | v2_struct_0(A_11366) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_35037,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_35003,c_35027])).

tff(c_35042,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_56,c_35037])).

tff(c_35043,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_35042])).

tff(c_68,plain,(
    ! [A_54] : k2_tarski(A_54,A_54) = k1_tarski(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    ! [D_6,B_2] : r2_hidden(D_6,k2_tarski(D_6,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_74,plain,(
    ! [A_54] : r2_hidden(A_54,k1_tarski(A_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_6])).

tff(c_54,plain,(
    r2_hidden('#skF_5',k2_orders_2('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_35005,plain,(
    r2_hidden('#skF_5',k2_orders_2('#skF_4',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35003,c_54])).

tff(c_43513,plain,(
    ! [B_16869,A_16870,C_16871] :
      ( ~ r2_hidden(B_16869,k2_orders_2(A_16870,C_16871))
      | ~ r2_hidden(B_16869,C_16871)
      | ~ m1_subset_1(C_16871,k1_zfmisc_1(u1_struct_0(A_16870)))
      | ~ m1_subset_1(B_16869,u1_struct_0(A_16870))
      | ~ l1_orders_2(A_16870)
      | ~ v5_orders_2(A_16870)
      | ~ v4_orders_2(A_16870)
      | ~ v3_orders_2(A_16870)
      | v2_struct_0(A_16870) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_43521,plain,
    ( ~ r2_hidden('#skF_5',k1_tarski('#skF_5'))
    | ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_35005,c_43513])).

tff(c_43525,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_56,c_35043,c_74,c_43521])).

tff(c_43527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_43525])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:44:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.65/5.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.65/5.92  
% 14.65/5.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.65/5.92  %$ r1_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 14.65/5.92  
% 14.65/5.92  %Foreground sorts:
% 14.65/5.92  
% 14.65/5.92  
% 14.65/5.92  %Background operators:
% 14.65/5.92  
% 14.65/5.92  
% 14.65/5.92  %Foreground operators:
% 14.65/5.92  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 14.65/5.92  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.65/5.92  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 14.65/5.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.65/5.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.65/5.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.65/5.92  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 14.65/5.92  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 14.65/5.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.65/5.92  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 14.65/5.92  tff('#skF_5', type, '#skF_5': $i).
% 14.65/5.92  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.65/5.92  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 14.65/5.92  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 14.65/5.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.65/5.92  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 14.65/5.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.65/5.92  tff('#skF_4', type, '#skF_4': $i).
% 14.65/5.92  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.65/5.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.65/5.92  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 14.65/5.92  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.65/5.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.65/5.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.65/5.92  
% 14.65/5.93  tff(f_163, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_orders_2)).
% 14.65/5.93  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 14.65/5.93  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 14.65/5.93  tff(f_123, axiom, (![A]: ((v3_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~(((?[D]: (((v6_orders_2(D, A) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) & r2_hidden(B, D)) & r2_hidden(C, D))) & ~r1_orders_2(A, B, C)) & ~r1_orders_2(A, C, B)) & ~((r1_orders_2(A, B, C) | r1_orders_2(A, C, B)) & (![D]: ((v6_orders_2(D, A) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~(r2_hidden(B, D) & r2_hidden(C, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_orders_2)).
% 14.65/5.93  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 14.65/5.93  tff(f_82, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 14.65/5.93  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 14.65/5.93  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 14.65/5.93  tff(f_145, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_orders_2)).
% 14.65/5.93  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.65/5.93  tff(c_64, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.65/5.93  tff(c_62, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.65/5.93  tff(c_60, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.65/5.93  tff(c_58, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.65/5.93  tff(c_56, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.65/5.93  tff(c_107, plain, (![A_66, B_67]: (k6_domain_1(A_66, B_67)=k1_tarski(B_67) | ~m1_subset_1(B_67, A_66) | v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.65/5.93  tff(c_111, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_107])).
% 14.65/5.93  tff(c_113, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_111])).
% 14.65/5.93  tff(c_114, plain, (![A_71, B_72]: (r1_orders_2(A_71, B_72, B_72) | ~m1_subset_1(B_72, u1_struct_0(A_71)) | ~l1_orders_2(A_71) | ~v3_orders_2(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.65/5.93  tff(c_116, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_5') | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_114])).
% 14.65/5.93  tff(c_119, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_58, c_116])).
% 14.65/5.93  tff(c_120, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_66, c_119])).
% 14.65/5.93  tff(c_40, plain, (![A_22, C_40, B_34]: (~r1_orders_2(A_22, C_40, B_34) | r2_hidden(B_34, '#skF_3'(A_22, B_34, C_40)) | ~m1_subset_1(C_40, u1_struct_0(A_22)) | ~m1_subset_1(B_34, u1_struct_0(A_22)) | ~l1_orders_2(A_22) | ~v3_orders_2(A_22))), inference(cnfTransformation, [status(thm)], [f_123])).
% 14.65/5.93  tff(c_3434, plain, (![A_3559, C_3560, B_3561]: (~r1_orders_2(A_3559, C_3560, B_3561) | m1_subset_1('#skF_3'(A_3559, B_3561, C_3560), k1_zfmisc_1(u1_struct_0(A_3559))) | ~m1_subset_1(C_3560, u1_struct_0(A_3559)) | ~m1_subset_1(B_3561, u1_struct_0(A_3559)) | ~l1_orders_2(A_3559) | ~v3_orders_2(A_3559))), inference(cnfTransformation, [status(thm)], [f_123])).
% 14.65/5.93  tff(c_24, plain, (![C_13, B_12, A_11]: (~v1_xboole_0(C_13) | ~m1_subset_1(B_12, k1_zfmisc_1(C_13)) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.65/5.93  tff(c_34954, plain, (![A_11094, A_11095, B_11096, C_11097]: (~v1_xboole_0(u1_struct_0(A_11094)) | ~r2_hidden(A_11095, '#skF_3'(A_11094, B_11096, C_11097)) | ~r1_orders_2(A_11094, C_11097, B_11096) | ~m1_subset_1(C_11097, u1_struct_0(A_11094)) | ~m1_subset_1(B_11096, u1_struct_0(A_11094)) | ~l1_orders_2(A_11094) | ~v3_orders_2(A_11094))), inference(resolution, [status(thm)], [c_3434, c_24])).
% 14.65/5.93  tff(c_34996, plain, (![A_11224, C_11225, B_11226]: (~v1_xboole_0(u1_struct_0(A_11224)) | ~r1_orders_2(A_11224, C_11225, B_11226) | ~m1_subset_1(C_11225, u1_struct_0(A_11224)) | ~m1_subset_1(B_11226, u1_struct_0(A_11224)) | ~l1_orders_2(A_11224) | ~v3_orders_2(A_11224))), inference(resolution, [status(thm)], [c_40, c_34954])).
% 14.65/5.93  tff(c_34998, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_120, c_34996])).
% 14.65/5.93  tff(c_35002, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_58, c_56, c_113, c_34998])).
% 14.65/5.94  tff(c_35003, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_111])).
% 14.65/5.94  tff(c_35027, plain, (![A_11366, B_11367]: (m1_subset_1(k6_domain_1(u1_struct_0(A_11366), B_11367), k1_zfmisc_1(u1_struct_0(A_11366))) | ~m1_subset_1(B_11367, u1_struct_0(A_11366)) | ~l1_orders_2(A_11366) | ~v3_orders_2(A_11366) | v2_struct_0(A_11366))), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.65/5.94  tff(c_35037, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_35003, c_35027])).
% 14.65/5.94  tff(c_35042, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_58, c_56, c_35037])).
% 14.65/5.94  tff(c_35043, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_35042])).
% 14.65/5.94  tff(c_68, plain, (![A_54]: (k2_tarski(A_54, A_54)=k1_tarski(A_54))), inference(cnfTransformation, [status(thm)], [f_36])).
% 14.65/5.94  tff(c_6, plain, (![D_6, B_2]: (r2_hidden(D_6, k2_tarski(D_6, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.65/5.94  tff(c_74, plain, (![A_54]: (r2_hidden(A_54, k1_tarski(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_6])).
% 14.65/5.94  tff(c_54, plain, (r2_hidden('#skF_5', k2_orders_2('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.65/5.94  tff(c_35005, plain, (r2_hidden('#skF_5', k2_orders_2('#skF_4', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_35003, c_54])).
% 14.65/5.94  tff(c_43513, plain, (![B_16869, A_16870, C_16871]: (~r2_hidden(B_16869, k2_orders_2(A_16870, C_16871)) | ~r2_hidden(B_16869, C_16871) | ~m1_subset_1(C_16871, k1_zfmisc_1(u1_struct_0(A_16870))) | ~m1_subset_1(B_16869, u1_struct_0(A_16870)) | ~l1_orders_2(A_16870) | ~v5_orders_2(A_16870) | ~v4_orders_2(A_16870) | ~v3_orders_2(A_16870) | v2_struct_0(A_16870))), inference(cnfTransformation, [status(thm)], [f_145])).
% 14.65/5.94  tff(c_43521, plain, (~r2_hidden('#skF_5', k1_tarski('#skF_5')) | ~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_35005, c_43513])).
% 14.65/5.94  tff(c_43525, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_56, c_35043, c_74, c_43521])).
% 14.65/5.94  tff(c_43527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_43525])).
% 14.65/5.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.65/5.94  
% 14.65/5.94  Inference rules
% 14.65/5.94  ----------------------
% 14.65/5.94  #Ref     : 0
% 14.65/5.94  #Sup     : 5997
% 14.65/5.94  #Fact    : 74
% 14.65/5.94  #Define  : 0
% 14.65/5.94  #Split   : 15
% 14.65/5.94  #Chain   : 0
% 14.65/5.94  #Close   : 0
% 14.65/5.94  
% 14.65/5.94  Ordering : KBO
% 14.65/5.94  
% 14.65/5.94  Simplification rules
% 14.65/5.94  ----------------------
% 14.65/5.94  #Subsume      : 1236
% 14.65/5.94  #Demod        : 519
% 14.65/5.94  #Tautology    : 744
% 14.65/5.94  #SimpNegUnit  : 272
% 14.65/5.94  #BackRed      : 1
% 14.65/5.94  
% 14.65/5.94  #Partial instantiations: 10109
% 14.65/5.94  #Strategies tried      : 1
% 14.65/5.94  
% 14.65/5.94  Timing (in seconds)
% 14.65/5.94  ----------------------
% 14.65/5.94  Preprocessing        : 0.36
% 14.65/5.94  Parsing              : 0.18
% 14.65/5.94  CNF conversion       : 0.03
% 14.65/5.94  Main loop            : 4.82
% 14.65/5.94  Inferencing          : 1.57
% 14.65/5.94  Reduction            : 0.81
% 14.65/5.94  Demodulation         : 0.55
% 14.65/5.94  BG Simplification    : 0.24
% 14.65/5.94  Subsumption          : 2.00
% 14.65/5.94  Abstraction          : 0.39
% 14.65/5.94  MUC search           : 0.00
% 14.65/5.94  Cooper               : 0.00
% 14.65/5.94  Total                : 5.20
% 14.65/5.94  Index Insertion      : 0.00
% 14.65/5.94  Index Deletion       : 0.00
% 14.65/5.94  Index Matching       : 0.00
% 14.65/5.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
