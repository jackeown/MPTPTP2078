%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:45 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 113 expanded)
%              Number of leaves         :   38 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  128 ( 211 expanded)
%              Number of equality atoms :   30 (  44 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_93,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_83,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_38,plain,(
    ! [A_20] : l1_orders_2(k2_yellow_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_50,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_54,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,(
    ! [A_22] :
      ( k6_domain_1(A_22,'#skF_3'(A_22)) = A_22
      | ~ v1_zfmisc_1(A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_48,plain,(
    ! [A_22] :
      ( m1_subset_1('#skF_3'(A_22),A_22)
      | ~ v1_zfmisc_1(A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_182,plain,(
    ! [A_62,B_63] :
      ( k6_domain_1(A_62,B_63) = k1_tarski(B_63)
      | ~ m1_subset_1(B_63,A_62)
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_230,plain,(
    ! [A_73] :
      ( k6_domain_1(A_73,'#skF_3'(A_73)) = k1_tarski('#skF_3'(A_73))
      | ~ v1_zfmisc_1(A_73)
      | v1_xboole_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_48,c_182])).

tff(c_287,plain,(
    ! [A_80] :
      ( k1_tarski('#skF_3'(A_80)) = A_80
      | ~ v1_zfmisc_1(A_80)
      | v1_xboole_0(A_80)
      | ~ v1_zfmisc_1(A_80)
      | v1_xboole_0(A_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_230])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [C_7] : r2_hidden(C_7,k1_tarski(C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_142,plain,(
    ! [C_50,B_51,A_52] :
      ( ~ v1_xboole_0(C_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(C_50))
      | ~ r2_hidden(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_150,plain,(
    ! [B_53,A_54,A_55] :
      ( ~ v1_xboole_0(B_53)
      | ~ r2_hidden(A_54,A_55)
      | ~ r1_tarski(A_55,B_53) ) ),
    inference(resolution,[status(thm)],[c_24,c_142])).

tff(c_166,plain,(
    ! [B_57,C_58] :
      ( ~ v1_xboole_0(B_57)
      | ~ r1_tarski(k1_tarski(C_58),B_57) ) ),
    inference(resolution,[status(thm)],[c_10,c_150])).

tff(c_171,plain,(
    ! [C_58] : ~ v1_xboole_0(k1_tarski(C_58)) ),
    inference(resolution,[status(thm)],[c_6,c_166])).

tff(c_123,plain,(
    ! [A_45,B_46] :
      ( r2_hidden(A_45,B_46)
      | v1_xboole_0(B_46)
      | ~ m1_subset_1(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( C_7 = A_3
      | ~ r2_hidden(C_7,k1_tarski(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_128,plain,(
    ! [A_45,A_3] :
      ( A_45 = A_3
      | v1_xboole_0(k1_tarski(A_3))
      | ~ m1_subset_1(A_45,k1_tarski(A_3)) ) ),
    inference(resolution,[status(thm)],[c_123,c_8])).

tff(c_173,plain,(
    ! [A_45,A_3] :
      ( A_45 = A_3
      | ~ m1_subset_1(A_45,k1_tarski(A_3)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_128])).

tff(c_404,plain,(
    ! [A_97,A_98] :
      ( A_97 = '#skF_3'(A_98)
      | ~ m1_subset_1(A_97,A_98)
      | ~ v1_zfmisc_1(A_98)
      | v1_xboole_0(A_98)
      | ~ v1_zfmisc_1(A_98)
      | v1_xboole_0(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_173])).

tff(c_413,plain,
    ( '#skF_3'('#skF_4') = '#skF_5'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_404])).

tff(c_419,plain,
    ( '#skF_3'('#skF_4') = '#skF_5'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_413])).

tff(c_420,plain,(
    '#skF_3'('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_419])).

tff(c_242,plain,(
    ! [A_22] :
      ( k1_tarski('#skF_3'(A_22)) = A_22
      | ~ v1_zfmisc_1(A_22)
      | v1_xboole_0(A_22)
      | ~ v1_zfmisc_1(A_22)
      | v1_xboole_0(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_230])).

tff(c_427,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_242])).

tff(c_443,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_427])).

tff(c_444,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_443])).

tff(c_191,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_182])).

tff(c_196,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_191])).

tff(c_52,plain,(
    v1_subset_1(k6_domain_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_197,plain,(
    v1_subset_1(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_52])).

tff(c_468,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_197])).

tff(c_40,plain,(
    ! [A_21] : u1_struct_0(k2_yellow_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_87,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_92,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_orders_2(A_37) ) ),
    inference(resolution,[status(thm)],[c_32,c_87])).

tff(c_95,plain,(
    ! [A_20] : u1_struct_0(k2_yellow_1(A_20)) = k2_struct_0(k2_yellow_1(A_20)) ),
    inference(resolution,[status(thm)],[c_38,c_92])).

tff(c_97,plain,(
    ! [A_20] : k2_struct_0(k2_yellow_1(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_95])).

tff(c_113,plain,(
    ! [A_43] :
      ( ~ v1_subset_1(k2_struct_0(A_43),u1_struct_0(A_43))
      | ~ l1_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_119,plain,(
    ! [A_21] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_21)),A_21)
      | ~ l1_struct_0(k2_yellow_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_113])).

tff(c_121,plain,(
    ! [A_21] :
      ( ~ v1_subset_1(A_21,A_21)
      | ~ l1_struct_0(k2_yellow_1(A_21)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_119])).

tff(c_500,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_468,c_121])).

tff(c_507,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_500])).

tff(c_511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:21:08 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.36  
% 2.61/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.36  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.61/1.36  
% 2.61/1.36  %Foreground sorts:
% 2.61/1.36  
% 2.61/1.36  
% 2.61/1.36  %Background operators:
% 2.61/1.36  
% 2.61/1.36  
% 2.61/1.36  %Foreground operators:
% 2.61/1.36  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.36  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.61/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.36  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.61/1.36  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.61/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.61/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.61/1.36  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.36  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.61/1.36  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.61/1.36  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.61/1.36  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.61/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.61/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.61/1.36  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.61/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.36  
% 2.61/1.38  tff(f_79, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.61/1.38  tff(f_68, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.61/1.38  tff(f_105, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.61/1.38  tff(f_93, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 2.61/1.38  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.61/1.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.61/1.38  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.61/1.38  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.61/1.38  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.61/1.38  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.61/1.38  tff(f_83, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.61/1.38  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.61/1.38  tff(f_64, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.61/1.38  tff(c_38, plain, (![A_20]: (l1_orders_2(k2_yellow_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.61/1.38  tff(c_32, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.61/1.38  tff(c_56, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.61/1.38  tff(c_50, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.61/1.38  tff(c_54, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.61/1.38  tff(c_46, plain, (![A_22]: (k6_domain_1(A_22, '#skF_3'(A_22))=A_22 | ~v1_zfmisc_1(A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.61/1.38  tff(c_48, plain, (![A_22]: (m1_subset_1('#skF_3'(A_22), A_22) | ~v1_zfmisc_1(A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.61/1.38  tff(c_182, plain, (![A_62, B_63]: (k6_domain_1(A_62, B_63)=k1_tarski(B_63) | ~m1_subset_1(B_63, A_62) | v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.61/1.38  tff(c_230, plain, (![A_73]: (k6_domain_1(A_73, '#skF_3'(A_73))=k1_tarski('#skF_3'(A_73)) | ~v1_zfmisc_1(A_73) | v1_xboole_0(A_73))), inference(resolution, [status(thm)], [c_48, c_182])).
% 2.61/1.38  tff(c_287, plain, (![A_80]: (k1_tarski('#skF_3'(A_80))=A_80 | ~v1_zfmisc_1(A_80) | v1_xboole_0(A_80) | ~v1_zfmisc_1(A_80) | v1_xboole_0(A_80))), inference(superposition, [status(thm), theory('equality')], [c_46, c_230])).
% 2.61/1.38  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.38  tff(c_10, plain, (![C_7]: (r2_hidden(C_7, k1_tarski(C_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.61/1.38  tff(c_24, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.61/1.38  tff(c_142, plain, (![C_50, B_51, A_52]: (~v1_xboole_0(C_50) | ~m1_subset_1(B_51, k1_zfmisc_1(C_50)) | ~r2_hidden(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.61/1.38  tff(c_150, plain, (![B_53, A_54, A_55]: (~v1_xboole_0(B_53) | ~r2_hidden(A_54, A_55) | ~r1_tarski(A_55, B_53))), inference(resolution, [status(thm)], [c_24, c_142])).
% 2.61/1.38  tff(c_166, plain, (![B_57, C_58]: (~v1_xboole_0(B_57) | ~r1_tarski(k1_tarski(C_58), B_57))), inference(resolution, [status(thm)], [c_10, c_150])).
% 2.61/1.38  tff(c_171, plain, (![C_58]: (~v1_xboole_0(k1_tarski(C_58)))), inference(resolution, [status(thm)], [c_6, c_166])).
% 2.61/1.38  tff(c_123, plain, (![A_45, B_46]: (r2_hidden(A_45, B_46) | v1_xboole_0(B_46) | ~m1_subset_1(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.61/1.38  tff(c_8, plain, (![C_7, A_3]: (C_7=A_3 | ~r2_hidden(C_7, k1_tarski(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.61/1.38  tff(c_128, plain, (![A_45, A_3]: (A_45=A_3 | v1_xboole_0(k1_tarski(A_3)) | ~m1_subset_1(A_45, k1_tarski(A_3)))), inference(resolution, [status(thm)], [c_123, c_8])).
% 2.61/1.38  tff(c_173, plain, (![A_45, A_3]: (A_45=A_3 | ~m1_subset_1(A_45, k1_tarski(A_3)))), inference(negUnitSimplification, [status(thm)], [c_171, c_128])).
% 2.61/1.38  tff(c_404, plain, (![A_97, A_98]: (A_97='#skF_3'(A_98) | ~m1_subset_1(A_97, A_98) | ~v1_zfmisc_1(A_98) | v1_xboole_0(A_98) | ~v1_zfmisc_1(A_98) | v1_xboole_0(A_98))), inference(superposition, [status(thm), theory('equality')], [c_287, c_173])).
% 2.61/1.38  tff(c_413, plain, ('#skF_3'('#skF_4')='#skF_5' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_404])).
% 2.61/1.38  tff(c_419, plain, ('#skF_3'('#skF_4')='#skF_5' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_413])).
% 2.61/1.38  tff(c_420, plain, ('#skF_3'('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_56, c_419])).
% 2.61/1.38  tff(c_242, plain, (![A_22]: (k1_tarski('#skF_3'(A_22))=A_22 | ~v1_zfmisc_1(A_22) | v1_xboole_0(A_22) | ~v1_zfmisc_1(A_22) | v1_xboole_0(A_22))), inference(superposition, [status(thm), theory('equality')], [c_46, c_230])).
% 2.61/1.38  tff(c_427, plain, (k1_tarski('#skF_5')='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_420, c_242])).
% 2.61/1.38  tff(c_443, plain, (k1_tarski('#skF_5')='#skF_4' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_427])).
% 2.61/1.38  tff(c_444, plain, (k1_tarski('#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_56, c_443])).
% 2.61/1.38  tff(c_191, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_182])).
% 2.61/1.38  tff(c_196, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_191])).
% 2.61/1.38  tff(c_52, plain, (v1_subset_1(k6_domain_1('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.61/1.38  tff(c_197, plain, (v1_subset_1(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_52])).
% 2.61/1.38  tff(c_468, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_444, c_197])).
% 2.61/1.38  tff(c_40, plain, (![A_21]: (u1_struct_0(k2_yellow_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.61/1.38  tff(c_87, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.61/1.38  tff(c_92, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_orders_2(A_37))), inference(resolution, [status(thm)], [c_32, c_87])).
% 2.61/1.38  tff(c_95, plain, (![A_20]: (u1_struct_0(k2_yellow_1(A_20))=k2_struct_0(k2_yellow_1(A_20)))), inference(resolution, [status(thm)], [c_38, c_92])).
% 2.61/1.38  tff(c_97, plain, (![A_20]: (k2_struct_0(k2_yellow_1(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_95])).
% 2.61/1.38  tff(c_113, plain, (![A_43]: (~v1_subset_1(k2_struct_0(A_43), u1_struct_0(A_43)) | ~l1_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.61/1.38  tff(c_119, plain, (![A_21]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_21)), A_21) | ~l1_struct_0(k2_yellow_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_113])).
% 2.61/1.38  tff(c_121, plain, (![A_21]: (~v1_subset_1(A_21, A_21) | ~l1_struct_0(k2_yellow_1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_119])).
% 2.61/1.38  tff(c_500, plain, (~l1_struct_0(k2_yellow_1('#skF_4'))), inference(resolution, [status(thm)], [c_468, c_121])).
% 2.61/1.38  tff(c_507, plain, (~l1_orders_2(k2_yellow_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_500])).
% 2.61/1.38  tff(c_511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_507])).
% 2.61/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.38  
% 2.61/1.38  Inference rules
% 2.61/1.38  ----------------------
% 2.61/1.38  #Ref     : 0
% 2.61/1.38  #Sup     : 102
% 2.61/1.38  #Fact    : 0
% 2.61/1.38  #Define  : 0
% 2.61/1.38  #Split   : 0
% 2.61/1.38  #Chain   : 0
% 2.61/1.38  #Close   : 0
% 2.61/1.38  
% 2.61/1.38  Ordering : KBO
% 2.61/1.38  
% 2.61/1.38  Simplification rules
% 2.61/1.38  ----------------------
% 2.61/1.38  #Subsume      : 7
% 2.61/1.38  #Demod        : 32
% 2.61/1.38  #Tautology    : 46
% 2.61/1.38  #SimpNegUnit  : 11
% 2.61/1.38  #BackRed      : 3
% 2.61/1.38  
% 2.61/1.38  #Partial instantiations: 0
% 2.61/1.38  #Strategies tried      : 1
% 2.61/1.38  
% 2.61/1.38  Timing (in seconds)
% 2.61/1.38  ----------------------
% 2.61/1.38  Preprocessing        : 0.32
% 2.61/1.38  Parsing              : 0.17
% 2.61/1.38  CNF conversion       : 0.02
% 2.61/1.38  Main loop            : 0.27
% 2.61/1.38  Inferencing          : 0.11
% 2.61/1.38  Reduction            : 0.08
% 2.61/1.38  Demodulation         : 0.05
% 2.61/1.38  BG Simplification    : 0.02
% 2.61/1.38  Subsumption          : 0.05
% 2.61/1.38  Abstraction          : 0.02
% 2.61/1.38  MUC search           : 0.00
% 2.61/1.38  Cooper               : 0.00
% 2.61/1.38  Total                : 0.63
% 2.61/1.38  Index Insertion      : 0.00
% 2.61/1.38  Index Deletion       : 0.00
% 2.61/1.38  Index Matching       : 0.00
% 2.61/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
