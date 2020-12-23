%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:32 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 102 expanded)
%              Number of leaves         :   40 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  122 ( 174 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_107,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_94,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_46,plain,(
    ! [A_30] : l1_orders_2(k2_yellow_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_54,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_58,plain,(
    m1_subset_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_30,plain,(
    ! [A_21,B_22] :
      ( r2_hidden(A_21,B_22)
      | v1_xboole_0(B_22)
      | ~ m1_subset_1(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    ! [C_14] : r2_hidden(C_14,k1_tarski(C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_92,plain,(
    ! [B_43,A_44] :
      ( ~ r2_hidden(B_43,A_44)
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [C_14] : ~ v1_xboole_0(k1_tarski(C_14)) ),
    inference(resolution,[status(thm)],[c_14,c_92])).

tff(c_175,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_2'(A_61,B_62),A_61)
      | r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_183,plain,(
    ! [A_10,B_62] :
      ( '#skF_2'(k1_tarski(A_10),B_62) = A_10
      | r1_tarski(k1_tarski(A_10),B_62) ) ),
    inference(resolution,[status(thm)],[c_175,c_12])).

tff(c_277,plain,(
    ! [B_85,A_86] :
      ( B_85 = A_86
      | ~ r1_tarski(A_86,B_85)
      | ~ v1_zfmisc_1(B_85)
      | v1_xboole_0(B_85)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_280,plain,(
    ! [A_10,B_62] :
      ( k1_tarski(A_10) = B_62
      | ~ v1_zfmisc_1(B_62)
      | v1_xboole_0(B_62)
      | v1_xboole_0(k1_tarski(A_10))
      | '#skF_2'(k1_tarski(A_10),B_62) = A_10 ) ),
    inference(resolution,[status(thm)],[c_183,c_277])).

tff(c_1490,plain,(
    ! [A_4207,B_4208] :
      ( k1_tarski(A_4207) = B_4208
      | ~ v1_zfmisc_1(B_4208)
      | v1_xboole_0(B_4208)
      | '#skF_2'(k1_tarski(A_4207),B_4208) = A_4207 ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_280])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2562,plain,(
    ! [A_7019,B_7020] :
      ( ~ r2_hidden(A_7019,B_7020)
      | r1_tarski(k1_tarski(A_7019),B_7020)
      | k1_tarski(A_7019) = B_7020
      | ~ v1_zfmisc_1(B_7020)
      | v1_xboole_0(B_7020) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1490,c_8])).

tff(c_52,plain,(
    ! [B_34,A_32] :
      ( B_34 = A_32
      | ~ r1_tarski(A_32,B_34)
      | ~ v1_zfmisc_1(B_34)
      | v1_xboole_0(B_34)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2584,plain,(
    ! [A_7019,B_7020] :
      ( v1_xboole_0(k1_tarski(A_7019))
      | ~ r2_hidden(A_7019,B_7020)
      | k1_tarski(A_7019) = B_7020
      | ~ v1_zfmisc_1(B_7020)
      | v1_xboole_0(B_7020) ) ),
    inference(resolution,[status(thm)],[c_2562,c_52])).

tff(c_2669,plain,(
    ! [A_7105,B_7106] :
      ( ~ r2_hidden(A_7105,B_7106)
      | k1_tarski(A_7105) = B_7106
      | ~ v1_zfmisc_1(B_7106)
      | v1_xboole_0(B_7106) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_2584])).

tff(c_2960,plain,(
    ! [A_7361,B_7362] :
      ( k1_tarski(A_7361) = B_7362
      | ~ v1_zfmisc_1(B_7362)
      | v1_xboole_0(B_7362)
      | ~ m1_subset_1(A_7361,B_7362) ) ),
    inference(resolution,[status(thm)],[c_30,c_2669])).

tff(c_2982,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_2960])).

tff(c_2986,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2982])).

tff(c_2987,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2986])).

tff(c_250,plain,(
    ! [A_81,B_82] :
      ( k6_domain_1(A_81,B_82) = k1_tarski(B_82)
      | ~ m1_subset_1(B_82,A_81)
      | v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_256,plain,
    ( k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_250])).

tff(c_260,plain,(
    k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_256])).

tff(c_56,plain,(
    v1_subset_1(k6_domain_1('#skF_5','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_261,plain,(
    v1_subset_1(k1_tarski('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_56])).

tff(c_2988,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2987,c_261])).

tff(c_48,plain,(
    ! [A_31] : u1_struct_0(k2_yellow_1(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_104,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_135,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_orders_2(A_51) ) ),
    inference(resolution,[status(thm)],[c_40,c_104])).

tff(c_138,plain,(
    ! [A_30] : u1_struct_0(k2_yellow_1(A_30)) = k2_struct_0(k2_yellow_1(A_30)) ),
    inference(resolution,[status(thm)],[c_46,c_135])).

tff(c_140,plain,(
    ! [A_30] : k2_struct_0(k2_yellow_1(A_30)) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_138])).

tff(c_151,plain,(
    ! [A_55] :
      ( ~ v1_subset_1(k2_struct_0(A_55),u1_struct_0(A_55))
      | ~ l1_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_157,plain,(
    ! [A_31] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_31)),A_31)
      | ~ l1_struct_0(k2_yellow_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_151])).

tff(c_159,plain,(
    ! [A_31] :
      ( ~ v1_subset_1(A_31,A_31)
      | ~ l1_struct_0(k2_yellow_1(A_31)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_157])).

tff(c_3085,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2988,c_159])).

tff(c_3151,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_3085])).

tff(c_3155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:50:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.87/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.69  
% 3.87/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.69  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.87/1.69  
% 3.87/1.69  %Foreground sorts:
% 3.87/1.69  
% 3.87/1.69  
% 3.87/1.69  %Background operators:
% 3.87/1.69  
% 3.87/1.69  
% 3.87/1.69  %Foreground operators:
% 3.87/1.69  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.87/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.87/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.87/1.69  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.87/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.87/1.69  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.87/1.69  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.87/1.69  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.87/1.69  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.87/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.87/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.87/1.69  tff('#skF_5', type, '#skF_5': $i).
% 3.87/1.69  tff('#skF_6', type, '#skF_6': $i).
% 3.87/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.87/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.87/1.69  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.87/1.69  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.87/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.87/1.69  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.87/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.87/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.87/1.69  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.87/1.69  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.87/1.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.87/1.69  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.87/1.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.87/1.69  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.87/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.87/1.69  
% 3.87/1.70  tff(f_90, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.87/1.70  tff(f_79, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.87/1.70  tff(f_119, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 3.87/1.70  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.87/1.70  tff(f_45, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.87/1.70  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.87/1.70  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.87/1.70  tff(f_107, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.87/1.70  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.87/1.70  tff(f_94, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.87/1.70  tff(f_70, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.87/1.70  tff(f_75, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_struct_0)).
% 3.87/1.70  tff(c_46, plain, (![A_30]: (l1_orders_2(k2_yellow_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.87/1.70  tff(c_40, plain, (![A_27]: (l1_struct_0(A_27) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.87/1.70  tff(c_60, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.87/1.70  tff(c_54, plain, (v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.87/1.70  tff(c_58, plain, (m1_subset_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.87/1.70  tff(c_30, plain, (![A_21, B_22]: (r2_hidden(A_21, B_22) | v1_xboole_0(B_22) | ~m1_subset_1(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.87/1.70  tff(c_14, plain, (![C_14]: (r2_hidden(C_14, k1_tarski(C_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.87/1.70  tff(c_92, plain, (![B_43, A_44]: (~r2_hidden(B_43, A_44) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.87/1.70  tff(c_96, plain, (![C_14]: (~v1_xboole_0(k1_tarski(C_14)))), inference(resolution, [status(thm)], [c_14, c_92])).
% 3.87/1.70  tff(c_175, plain, (![A_61, B_62]: (r2_hidden('#skF_2'(A_61, B_62), A_61) | r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.87/1.70  tff(c_12, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.87/1.70  tff(c_183, plain, (![A_10, B_62]: ('#skF_2'(k1_tarski(A_10), B_62)=A_10 | r1_tarski(k1_tarski(A_10), B_62))), inference(resolution, [status(thm)], [c_175, c_12])).
% 3.87/1.70  tff(c_277, plain, (![B_85, A_86]: (B_85=A_86 | ~r1_tarski(A_86, B_85) | ~v1_zfmisc_1(B_85) | v1_xboole_0(B_85) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.87/1.70  tff(c_280, plain, (![A_10, B_62]: (k1_tarski(A_10)=B_62 | ~v1_zfmisc_1(B_62) | v1_xboole_0(B_62) | v1_xboole_0(k1_tarski(A_10)) | '#skF_2'(k1_tarski(A_10), B_62)=A_10)), inference(resolution, [status(thm)], [c_183, c_277])).
% 3.87/1.70  tff(c_1490, plain, (![A_4207, B_4208]: (k1_tarski(A_4207)=B_4208 | ~v1_zfmisc_1(B_4208) | v1_xboole_0(B_4208) | '#skF_2'(k1_tarski(A_4207), B_4208)=A_4207)), inference(negUnitSimplification, [status(thm)], [c_96, c_280])).
% 3.87/1.70  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.87/1.70  tff(c_2562, plain, (![A_7019, B_7020]: (~r2_hidden(A_7019, B_7020) | r1_tarski(k1_tarski(A_7019), B_7020) | k1_tarski(A_7019)=B_7020 | ~v1_zfmisc_1(B_7020) | v1_xboole_0(B_7020))), inference(superposition, [status(thm), theory('equality')], [c_1490, c_8])).
% 3.87/1.70  tff(c_52, plain, (![B_34, A_32]: (B_34=A_32 | ~r1_tarski(A_32, B_34) | ~v1_zfmisc_1(B_34) | v1_xboole_0(B_34) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.87/1.70  tff(c_2584, plain, (![A_7019, B_7020]: (v1_xboole_0(k1_tarski(A_7019)) | ~r2_hidden(A_7019, B_7020) | k1_tarski(A_7019)=B_7020 | ~v1_zfmisc_1(B_7020) | v1_xboole_0(B_7020))), inference(resolution, [status(thm)], [c_2562, c_52])).
% 3.87/1.70  tff(c_2669, plain, (![A_7105, B_7106]: (~r2_hidden(A_7105, B_7106) | k1_tarski(A_7105)=B_7106 | ~v1_zfmisc_1(B_7106) | v1_xboole_0(B_7106))), inference(negUnitSimplification, [status(thm)], [c_96, c_2584])).
% 3.87/1.70  tff(c_2960, plain, (![A_7361, B_7362]: (k1_tarski(A_7361)=B_7362 | ~v1_zfmisc_1(B_7362) | v1_xboole_0(B_7362) | ~m1_subset_1(A_7361, B_7362))), inference(resolution, [status(thm)], [c_30, c_2669])).
% 3.87/1.70  tff(c_2982, plain, (k1_tarski('#skF_6')='#skF_5' | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_58, c_2960])).
% 3.87/1.70  tff(c_2986, plain, (k1_tarski('#skF_6')='#skF_5' | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2982])).
% 3.87/1.70  tff(c_2987, plain, (k1_tarski('#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_60, c_2986])).
% 3.87/1.70  tff(c_250, plain, (![A_81, B_82]: (k6_domain_1(A_81, B_82)=k1_tarski(B_82) | ~m1_subset_1(B_82, A_81) | v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.87/1.70  tff(c_256, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_58, c_250])).
% 3.87/1.70  tff(c_260, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_60, c_256])).
% 3.87/1.70  tff(c_56, plain, (v1_subset_1(k6_domain_1('#skF_5', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.87/1.70  tff(c_261, plain, (v1_subset_1(k1_tarski('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_56])).
% 3.87/1.70  tff(c_2988, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2987, c_261])).
% 3.87/1.70  tff(c_48, plain, (![A_31]: (u1_struct_0(k2_yellow_1(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.87/1.70  tff(c_104, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.87/1.70  tff(c_135, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_orders_2(A_51))), inference(resolution, [status(thm)], [c_40, c_104])).
% 3.87/1.70  tff(c_138, plain, (![A_30]: (u1_struct_0(k2_yellow_1(A_30))=k2_struct_0(k2_yellow_1(A_30)))), inference(resolution, [status(thm)], [c_46, c_135])).
% 3.87/1.70  tff(c_140, plain, (![A_30]: (k2_struct_0(k2_yellow_1(A_30))=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_138])).
% 3.87/1.70  tff(c_151, plain, (![A_55]: (~v1_subset_1(k2_struct_0(A_55), u1_struct_0(A_55)) | ~l1_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.87/1.70  tff(c_157, plain, (![A_31]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_31)), A_31) | ~l1_struct_0(k2_yellow_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_151])).
% 3.87/1.70  tff(c_159, plain, (![A_31]: (~v1_subset_1(A_31, A_31) | ~l1_struct_0(k2_yellow_1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_157])).
% 3.87/1.70  tff(c_3085, plain, (~l1_struct_0(k2_yellow_1('#skF_5'))), inference(resolution, [status(thm)], [c_2988, c_159])).
% 3.87/1.70  tff(c_3151, plain, (~l1_orders_2(k2_yellow_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_3085])).
% 3.87/1.70  tff(c_3155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_3151])).
% 3.87/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.70  
% 3.87/1.70  Inference rules
% 3.87/1.70  ----------------------
% 3.87/1.70  #Ref     : 0
% 3.87/1.70  #Sup     : 364
% 3.87/1.70  #Fact    : 0
% 3.87/1.70  #Define  : 0
% 3.87/1.70  #Split   : 3
% 3.87/1.70  #Chain   : 0
% 3.87/1.70  #Close   : 0
% 3.87/1.70  
% 3.87/1.70  Ordering : KBO
% 3.87/1.70  
% 3.87/1.70  Simplification rules
% 3.87/1.70  ----------------------
% 3.87/1.70  #Subsume      : 76
% 3.87/1.70  #Demod        : 32
% 3.87/1.70  #Tautology    : 101
% 3.87/1.70  #SimpNegUnit  : 44
% 3.87/1.70  #BackRed      : 3
% 3.87/1.70  
% 3.87/1.70  #Partial instantiations: 4004
% 3.87/1.70  #Strategies tried      : 1
% 3.87/1.70  
% 3.87/1.70  Timing (in seconds)
% 3.87/1.70  ----------------------
% 4.14/1.71  Preprocessing        : 0.32
% 4.14/1.71  Parsing              : 0.16
% 4.14/1.71  CNF conversion       : 0.02
% 4.14/1.71  Main loop            : 0.63
% 4.14/1.71  Inferencing          : 0.33
% 4.14/1.71  Reduction            : 0.13
% 4.14/1.71  Demodulation         : 0.08
% 4.14/1.71  BG Simplification    : 0.03
% 4.14/1.71  Subsumption          : 0.09
% 4.14/1.71  Abstraction          : 0.03
% 4.14/1.71  MUC search           : 0.00
% 4.14/1.71  Cooper               : 0.00
% 4.14/1.71  Total                : 0.98
% 4.14/1.71  Index Insertion      : 0.00
% 4.14/1.71  Index Deletion       : 0.00
% 4.14/1.71  Index Matching       : 0.00
% 4.14/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
