%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:22 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 489 expanded)
%              Number of leaves         :   45 ( 171 expanded)
%              Depth                    :   18
%              Number of atoms          :  184 (1234 expanded)
%              Number of equality atoms :   16 ( 151 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r7_relat_2 > r2_hidden > r1_relat_2 > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_tarski > #skF_6 > #skF_4 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(r7_relat_2,type,(
    r7_relat_2: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
              & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_orders_2(A)
      <=> r1_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_orders_2)).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_109,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r7_relat_2(A,B)
        <=> ! [C,D] :
              ~ ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & ~ r2_hidden(k4_tarski(C,D),A)
                & ~ r2_hidden(k4_tarski(D,C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_relat_2(A,B)
        <=> ! [C] :
              ( r2_hidden(C,B)
             => r2_hidden(k4_tarski(C,C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_2)).

tff(c_78,plain,(
    l1_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_68,plain,(
    ! [A_56] :
      ( l1_struct_0(A_56)
      | ~ l1_orders_2(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_76,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1182,plain,(
    ! [A_2121,B_2122] :
      ( k6_domain_1(A_2121,B_2122) = k1_tarski(B_2122)
      | ~ m1_subset_1(B_2122,A_2121)
      | v1_xboole_0(A_2121) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1186,plain,
    ( k6_domain_1(u1_struct_0('#skF_8'),'#skF_9') = k1_tarski('#skF_9')
    | v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_76,c_1182])).

tff(c_1187,plain,(
    v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1186])).

tff(c_46,plain,(
    ! [A_32] :
      ( ~ v1_xboole_0(u1_struct_0(A_32))
      | ~ l1_struct_0(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1190,plain,
    ( ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1187,c_46])).

tff(c_1193,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1190])).

tff(c_1196,plain,(
    ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_1193])).

tff(c_1200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1196])).

tff(c_1202,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1186])).

tff(c_1201,plain,(
    k6_domain_1(u1_struct_0('#skF_8'),'#skF_9') = k1_tarski('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1186])).

tff(c_80,plain,(
    v3_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_54,plain,(
    ! [A_36] :
      ( r1_relat_2(u1_orders_2(A_36),u1_struct_0(A_36))
      | ~ v3_orders_2(A_36)
      | ~ l1_orders_2(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_212,plain,(
    ! [A_91] :
      ( m1_subset_1(u1_orders_2(A_91),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_91),u1_struct_0(A_91))))
      | ~ l1_orders_2(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_36,plain,(
    ! [B_19,A_17] :
      ( v1_relat_1(B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_17))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_218,plain,(
    ! [A_91] :
      ( v1_relat_1(u1_orders_2(A_91))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_91),u1_struct_0(A_91)))
      | ~ l1_orders_2(A_91) ) ),
    inference(resolution,[status(thm)],[c_212,c_36])).

tff(c_222,plain,(
    ! [A_91] :
      ( v1_relat_1(u1_orders_2(A_91))
      | ~ l1_orders_2(A_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_218])).

tff(c_134,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_7'(A_80,B_81),B_81)
      | r7_relat_2(A_80,B_81)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_144,plain,(
    ! [A_80,A_1] :
      ( '#skF_7'(A_80,k1_tarski(A_1)) = A_1
      | r7_relat_2(A_80,k1_tarski(A_1))
      | ~ v1_relat_1(A_80) ) ),
    inference(resolution,[status(thm)],[c_134,c_2])).

tff(c_167,plain,(
    ! [A_86,B_87] :
      ( k6_domain_1(A_86,B_87) = k1_tarski(B_87)
      | ~ m1_subset_1(B_87,A_86)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_171,plain,
    ( k6_domain_1(u1_struct_0('#skF_8'),'#skF_9') = k1_tarski('#skF_9')
    | v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_76,c_167])).

tff(c_172,plain,(
    v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_175,plain,
    ( ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_172,c_46])).

tff(c_178,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_175])).

tff(c_181,plain,(
    ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_178])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_181])).

tff(c_186,plain,(
    k6_domain_1(u1_struct_0('#skF_8'),'#skF_9') = k1_tarski('#skF_9') ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_74,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_8'),'#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ v6_orders_2(k6_domain_1(u1_struct_0('#skF_8'),'#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_100,plain,(
    ~ v6_orders_2(k6_domain_1(u1_struct_0('#skF_8'),'#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_207,plain,(
    ~ v6_orders_2(k1_tarski('#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_100])).

tff(c_187,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_233,plain,(
    ! [A_101,B_102] :
      ( m1_subset_1(k6_domain_1(A_101,B_102),k1_zfmisc_1(A_101))
      | ~ m1_subset_1(B_102,A_101)
      | v1_xboole_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_242,plain,
    ( m1_subset_1(k1_tarski('#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
    | v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_233])).

tff(c_246,plain,
    ( m1_subset_1(k1_tarski('#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_8')))
    | v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_242])).

tff(c_247,plain,(
    m1_subset_1(k1_tarski('#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_246])).

tff(c_1025,plain,(
    ! [B_1824,A_1825] :
      ( v6_orders_2(B_1824,A_1825)
      | ~ r7_relat_2(u1_orders_2(A_1825),B_1824)
      | ~ m1_subset_1(B_1824,k1_zfmisc_1(u1_struct_0(A_1825)))
      | ~ l1_orders_2(A_1825) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1034,plain,
    ( v6_orders_2(k1_tarski('#skF_9'),'#skF_8')
    | ~ r7_relat_2(u1_orders_2('#skF_8'),k1_tarski('#skF_9'))
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_247,c_1025])).

tff(c_1041,plain,
    ( v6_orders_2(k1_tarski('#skF_9'),'#skF_8')
    | ~ r7_relat_2(u1_orders_2('#skF_8'),k1_tarski('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1034])).

tff(c_1042,plain,(
    ~ r7_relat_2(u1_orders_2('#skF_8'),k1_tarski('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_1041])).

tff(c_1050,plain,
    ( '#skF_7'(u1_orders_2('#skF_8'),k1_tarski('#skF_9')) = '#skF_9'
    | ~ v1_relat_1(u1_orders_2('#skF_8')) ),
    inference(resolution,[status(thm)],[c_144,c_1042])).

tff(c_1052,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1050])).

tff(c_1055,plain,(
    ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_222,c_1052])).

tff(c_1059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1055])).

tff(c_1061,plain,(
    v1_relat_1(u1_orders_2('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1050])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_188,plain,(
    ! [C_88,A_89,B_90] :
      ( r2_hidden(C_88,A_89)
      | ~ r2_hidden(C_88,B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_206,plain,(
    ! [C_5,A_89] :
      ( r2_hidden(C_5,A_89)
      | ~ m1_subset_1(k1_tarski(C_5),k1_zfmisc_1(A_89)) ) ),
    inference(resolution,[status(thm)],[c_4,c_188])).

tff(c_258,plain,(
    r2_hidden('#skF_9',u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_247,c_206])).

tff(c_292,plain,(
    ! [C_118,A_119,B_120] :
      ( r2_hidden(k4_tarski(C_118,C_118),A_119)
      | ~ r2_hidden(C_118,B_120)
      | ~ r1_relat_2(A_119,B_120)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_310,plain,(
    ! [A_119] :
      ( r2_hidden(k4_tarski('#skF_9','#skF_9'),A_119)
      | ~ r1_relat_2(A_119,u1_struct_0('#skF_8'))
      | ~ v1_relat_1(A_119) ) ),
    inference(resolution,[status(thm)],[c_258,c_292])).

tff(c_1060,plain,(
    '#skF_7'(u1_orders_2('#skF_8'),k1_tarski('#skF_9')) = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1050])).

tff(c_156,plain,(
    ! [A_84,B_85] :
      ( r2_hidden('#skF_6'(A_84,B_85),B_85)
      | r7_relat_2(A_84,B_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_166,plain,(
    ! [A_84,A_1] :
      ( '#skF_6'(A_84,k1_tarski(A_1)) = A_1
      | r7_relat_2(A_84,k1_tarski(A_1))
      | ~ v1_relat_1(A_84) ) ),
    inference(resolution,[status(thm)],[c_156,c_2])).

tff(c_1051,plain,
    ( '#skF_6'(u1_orders_2('#skF_8'),k1_tarski('#skF_9')) = '#skF_9'
    | ~ v1_relat_1(u1_orders_2('#skF_8')) ),
    inference(resolution,[status(thm)],[c_166,c_1042])).

tff(c_1062,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1051])).

tff(c_1064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_1062])).

tff(c_1065,plain,(
    '#skF_6'(u1_orders_2('#skF_8'),k1_tarski('#skF_9')) = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1051])).

tff(c_60,plain,(
    ! [A_37,B_47] :
      ( ~ r2_hidden(k4_tarski('#skF_6'(A_37,B_47),'#skF_7'(A_37,B_47)),A_37)
      | r7_relat_2(A_37,B_47)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1101,plain,
    ( ~ r2_hidden(k4_tarski('#skF_9','#skF_7'(u1_orders_2('#skF_8'),k1_tarski('#skF_9'))),u1_orders_2('#skF_8'))
    | r7_relat_2(u1_orders_2('#skF_8'),k1_tarski('#skF_9'))
    | ~ v1_relat_1(u1_orders_2('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1065,c_60])).

tff(c_1114,plain,
    ( ~ r2_hidden(k4_tarski('#skF_9','#skF_9'),u1_orders_2('#skF_8'))
    | r7_relat_2(u1_orders_2('#skF_8'),k1_tarski('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_1060,c_1101])).

tff(c_1115,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_9'),u1_orders_2('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_1042,c_1114])).

tff(c_1130,plain,
    ( ~ r1_relat_2(u1_orders_2('#skF_8'),u1_struct_0('#skF_8'))
    | ~ v1_relat_1(u1_orders_2('#skF_8')) ),
    inference(resolution,[status(thm)],[c_310,c_1115])).

tff(c_1136,plain,(
    ~ r1_relat_2(u1_orders_2('#skF_8'),u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_1130])).

tff(c_1142,plain,
    ( ~ v3_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_1136])).

tff(c_1146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_80,c_1142])).

tff(c_1147,plain,(
    ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_8'),'#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1203,plain,(
    ~ m1_subset_1(k1_tarski('#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1201,c_1147])).

tff(c_1283,plain,(
    ! [A_2144,B_2145] :
      ( m1_subset_1(k6_domain_1(A_2144,B_2145),k1_zfmisc_1(A_2144))
      | ~ m1_subset_1(B_2145,A_2144)
      | v1_xboole_0(A_2144) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1292,plain,
    ( m1_subset_1(k1_tarski('#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
    | v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1201,c_1283])).

tff(c_1296,plain,
    ( m1_subset_1(k1_tarski('#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_8')))
    | v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1292])).

tff(c_1298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1202,c_1203,c_1296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:03:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.59  
% 3.59/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.59  %$ v6_orders_2 > r7_relat_2 > r2_hidden > r1_relat_2 > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_tarski > #skF_6 > #skF_4 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_5
% 3.59/1.59  
% 3.59/1.59  %Foreground sorts:
% 3.59/1.59  
% 3.59/1.59  
% 3.59/1.59  %Background operators:
% 3.59/1.59  
% 3.59/1.59  
% 3.59/1.59  %Foreground operators:
% 3.59/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.59/1.59  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.59/1.59  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.59/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.59/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.59/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.59/1.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.59/1.59  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.59/1.59  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 3.59/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.59/1.59  tff('#skF_9', type, '#skF_9': $i).
% 3.59/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.59/1.59  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.59/1.59  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.59/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.59/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.59/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.59/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.59/1.59  tff(r7_relat_2, type, r7_relat_2: ($i * $i) > $o).
% 3.59/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.59/1.59  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.59/1.59  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.59/1.59  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.59/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.59/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.59/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.59/1.59  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.59/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.59/1.59  
% 3.59/1.61  tff(f_146, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 3.59/1.61  tff(f_120, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.59/1.61  tff(f_131, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.59/1.61  tff(f_77, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.59/1.61  tff(f_92, axiom, (![A]: (l1_orders_2(A) => (v3_orders_2(A) <=> r1_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_orders_2)).
% 3.59/1.61  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.59/1.61  tff(f_124, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 3.59/1.61  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.59/1.61  tff(f_109, axiom, (![A]: (v1_relat_1(A) => (![B]: (r7_relat_2(A, B) <=> (![C, D]: ~(((r2_hidden(C, B) & r2_hidden(D, B)) & ~r2_hidden(k4_tarski(C, D), A)) & ~r2_hidden(k4_tarski(D, C), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_relat_2)).
% 3.59/1.61  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.59/1.61  tff(f_116, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.59/1.61  tff(f_86, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_orders_2(B, A) <=> r7_relat_2(u1_orders_2(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_orders_2)).
% 3.59/1.61  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.59/1.61  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_relat_2(A, B) <=> (![C]: (r2_hidden(C, B) => r2_hidden(k4_tarski(C, C), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_2)).
% 3.59/1.61  tff(c_78, plain, (l1_orders_2('#skF_8')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.59/1.61  tff(c_68, plain, (![A_56]: (l1_struct_0(A_56) | ~l1_orders_2(A_56))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.59/1.61  tff(c_82, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.59/1.61  tff(c_76, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.59/1.61  tff(c_1182, plain, (![A_2121, B_2122]: (k6_domain_1(A_2121, B_2122)=k1_tarski(B_2122) | ~m1_subset_1(B_2122, A_2121) | v1_xboole_0(A_2121))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.59/1.61  tff(c_1186, plain, (k6_domain_1(u1_struct_0('#skF_8'), '#skF_9')=k1_tarski('#skF_9') | v1_xboole_0(u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_76, c_1182])).
% 3.59/1.61  tff(c_1187, plain, (v1_xboole_0(u1_struct_0('#skF_8'))), inference(splitLeft, [status(thm)], [c_1186])).
% 3.59/1.61  tff(c_46, plain, (![A_32]: (~v1_xboole_0(u1_struct_0(A_32)) | ~l1_struct_0(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.59/1.61  tff(c_1190, plain, (~l1_struct_0('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_1187, c_46])).
% 3.59/1.61  tff(c_1193, plain, (~l1_struct_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_82, c_1190])).
% 3.59/1.61  tff(c_1196, plain, (~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_68, c_1193])).
% 3.59/1.61  tff(c_1200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_1196])).
% 3.59/1.61  tff(c_1202, plain, (~v1_xboole_0(u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_1186])).
% 3.59/1.61  tff(c_1201, plain, (k6_domain_1(u1_struct_0('#skF_8'), '#skF_9')=k1_tarski('#skF_9')), inference(splitRight, [status(thm)], [c_1186])).
% 3.59/1.61  tff(c_80, plain, (v3_orders_2('#skF_8')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.59/1.61  tff(c_54, plain, (![A_36]: (r1_relat_2(u1_orders_2(A_36), u1_struct_0(A_36)) | ~v3_orders_2(A_36) | ~l1_orders_2(A_36))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.59/1.61  tff(c_38, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.59/1.61  tff(c_212, plain, (![A_91]: (m1_subset_1(u1_orders_2(A_91), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_91), u1_struct_0(A_91)))) | ~l1_orders_2(A_91))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.59/1.61  tff(c_36, plain, (![B_19, A_17]: (v1_relat_1(B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(A_17)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.59/1.61  tff(c_218, plain, (![A_91]: (v1_relat_1(u1_orders_2(A_91)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_91), u1_struct_0(A_91))) | ~l1_orders_2(A_91))), inference(resolution, [status(thm)], [c_212, c_36])).
% 3.59/1.61  tff(c_222, plain, (![A_91]: (v1_relat_1(u1_orders_2(A_91)) | ~l1_orders_2(A_91))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_218])).
% 3.59/1.61  tff(c_134, plain, (![A_80, B_81]: (r2_hidden('#skF_7'(A_80, B_81), B_81) | r7_relat_2(A_80, B_81) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.59/1.61  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.59/1.61  tff(c_144, plain, (![A_80, A_1]: ('#skF_7'(A_80, k1_tarski(A_1))=A_1 | r7_relat_2(A_80, k1_tarski(A_1)) | ~v1_relat_1(A_80))), inference(resolution, [status(thm)], [c_134, c_2])).
% 3.59/1.61  tff(c_167, plain, (![A_86, B_87]: (k6_domain_1(A_86, B_87)=k1_tarski(B_87) | ~m1_subset_1(B_87, A_86) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.59/1.61  tff(c_171, plain, (k6_domain_1(u1_struct_0('#skF_8'), '#skF_9')=k1_tarski('#skF_9') | v1_xboole_0(u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_76, c_167])).
% 3.59/1.61  tff(c_172, plain, (v1_xboole_0(u1_struct_0('#skF_8'))), inference(splitLeft, [status(thm)], [c_171])).
% 3.59/1.61  tff(c_175, plain, (~l1_struct_0('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_172, c_46])).
% 3.59/1.61  tff(c_178, plain, (~l1_struct_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_82, c_175])).
% 3.59/1.61  tff(c_181, plain, (~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_68, c_178])).
% 3.59/1.61  tff(c_185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_181])).
% 3.59/1.61  tff(c_186, plain, (k6_domain_1(u1_struct_0('#skF_8'), '#skF_9')=k1_tarski('#skF_9')), inference(splitRight, [status(thm)], [c_171])).
% 3.59/1.61  tff(c_74, plain, (~m1_subset_1(k6_domain_1(u1_struct_0('#skF_8'), '#skF_9'), k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~v6_orders_2(k6_domain_1(u1_struct_0('#skF_8'), '#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.59/1.61  tff(c_100, plain, (~v6_orders_2(k6_domain_1(u1_struct_0('#skF_8'), '#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_74])).
% 3.59/1.61  tff(c_207, plain, (~v6_orders_2(k1_tarski('#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_100])).
% 3.59/1.61  tff(c_187, plain, (~v1_xboole_0(u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_171])).
% 3.59/1.61  tff(c_233, plain, (![A_101, B_102]: (m1_subset_1(k6_domain_1(A_101, B_102), k1_zfmisc_1(A_101)) | ~m1_subset_1(B_102, A_101) | v1_xboole_0(A_101))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.59/1.61  tff(c_242, plain, (m1_subset_1(k1_tarski('#skF_9'), k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | v1_xboole_0(u1_struct_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_233])).
% 3.59/1.61  tff(c_246, plain, (m1_subset_1(k1_tarski('#skF_9'), k1_zfmisc_1(u1_struct_0('#skF_8'))) | v1_xboole_0(u1_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_242])).
% 3.59/1.61  tff(c_247, plain, (m1_subset_1(k1_tarski('#skF_9'), k1_zfmisc_1(u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_187, c_246])).
% 3.59/1.61  tff(c_1025, plain, (![B_1824, A_1825]: (v6_orders_2(B_1824, A_1825) | ~r7_relat_2(u1_orders_2(A_1825), B_1824) | ~m1_subset_1(B_1824, k1_zfmisc_1(u1_struct_0(A_1825))) | ~l1_orders_2(A_1825))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.59/1.61  tff(c_1034, plain, (v6_orders_2(k1_tarski('#skF_9'), '#skF_8') | ~r7_relat_2(u1_orders_2('#skF_8'), k1_tarski('#skF_9')) | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_247, c_1025])).
% 3.59/1.61  tff(c_1041, plain, (v6_orders_2(k1_tarski('#skF_9'), '#skF_8') | ~r7_relat_2(u1_orders_2('#skF_8'), k1_tarski('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1034])).
% 3.59/1.61  tff(c_1042, plain, (~r7_relat_2(u1_orders_2('#skF_8'), k1_tarski('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_207, c_1041])).
% 3.59/1.61  tff(c_1050, plain, ('#skF_7'(u1_orders_2('#skF_8'), k1_tarski('#skF_9'))='#skF_9' | ~v1_relat_1(u1_orders_2('#skF_8'))), inference(resolution, [status(thm)], [c_144, c_1042])).
% 3.59/1.61  tff(c_1052, plain, (~v1_relat_1(u1_orders_2('#skF_8'))), inference(splitLeft, [status(thm)], [c_1050])).
% 3.59/1.61  tff(c_1055, plain, (~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_222, c_1052])).
% 3.59/1.61  tff(c_1059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_1055])).
% 3.59/1.61  tff(c_1061, plain, (v1_relat_1(u1_orders_2('#skF_8'))), inference(splitRight, [status(thm)], [c_1050])).
% 3.59/1.61  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.59/1.61  tff(c_188, plain, (![C_88, A_89, B_90]: (r2_hidden(C_88, A_89) | ~r2_hidden(C_88, B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.59/1.61  tff(c_206, plain, (![C_5, A_89]: (r2_hidden(C_5, A_89) | ~m1_subset_1(k1_tarski(C_5), k1_zfmisc_1(A_89)))), inference(resolution, [status(thm)], [c_4, c_188])).
% 3.59/1.61  tff(c_258, plain, (r2_hidden('#skF_9', u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_247, c_206])).
% 3.59/1.61  tff(c_292, plain, (![C_118, A_119, B_120]: (r2_hidden(k4_tarski(C_118, C_118), A_119) | ~r2_hidden(C_118, B_120) | ~r1_relat_2(A_119, B_120) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.59/1.61  tff(c_310, plain, (![A_119]: (r2_hidden(k4_tarski('#skF_9', '#skF_9'), A_119) | ~r1_relat_2(A_119, u1_struct_0('#skF_8')) | ~v1_relat_1(A_119))), inference(resolution, [status(thm)], [c_258, c_292])).
% 3.59/1.61  tff(c_1060, plain, ('#skF_7'(u1_orders_2('#skF_8'), k1_tarski('#skF_9'))='#skF_9'), inference(splitRight, [status(thm)], [c_1050])).
% 3.59/1.61  tff(c_156, plain, (![A_84, B_85]: (r2_hidden('#skF_6'(A_84, B_85), B_85) | r7_relat_2(A_84, B_85) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.59/1.61  tff(c_166, plain, (![A_84, A_1]: ('#skF_6'(A_84, k1_tarski(A_1))=A_1 | r7_relat_2(A_84, k1_tarski(A_1)) | ~v1_relat_1(A_84))), inference(resolution, [status(thm)], [c_156, c_2])).
% 3.59/1.61  tff(c_1051, plain, ('#skF_6'(u1_orders_2('#skF_8'), k1_tarski('#skF_9'))='#skF_9' | ~v1_relat_1(u1_orders_2('#skF_8'))), inference(resolution, [status(thm)], [c_166, c_1042])).
% 3.59/1.61  tff(c_1062, plain, (~v1_relat_1(u1_orders_2('#skF_8'))), inference(splitLeft, [status(thm)], [c_1051])).
% 3.59/1.61  tff(c_1064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1061, c_1062])).
% 3.59/1.61  tff(c_1065, plain, ('#skF_6'(u1_orders_2('#skF_8'), k1_tarski('#skF_9'))='#skF_9'), inference(splitRight, [status(thm)], [c_1051])).
% 3.59/1.61  tff(c_60, plain, (![A_37, B_47]: (~r2_hidden(k4_tarski('#skF_6'(A_37, B_47), '#skF_7'(A_37, B_47)), A_37) | r7_relat_2(A_37, B_47) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.59/1.61  tff(c_1101, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_7'(u1_orders_2('#skF_8'), k1_tarski('#skF_9'))), u1_orders_2('#skF_8')) | r7_relat_2(u1_orders_2('#skF_8'), k1_tarski('#skF_9')) | ~v1_relat_1(u1_orders_2('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1065, c_60])).
% 3.59/1.61  tff(c_1114, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_9'), u1_orders_2('#skF_8')) | r7_relat_2(u1_orders_2('#skF_8'), k1_tarski('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_1060, c_1101])).
% 3.59/1.61  tff(c_1115, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_9'), u1_orders_2('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1042, c_1114])).
% 3.59/1.61  tff(c_1130, plain, (~r1_relat_2(u1_orders_2('#skF_8'), u1_struct_0('#skF_8')) | ~v1_relat_1(u1_orders_2('#skF_8'))), inference(resolution, [status(thm)], [c_310, c_1115])).
% 3.59/1.61  tff(c_1136, plain, (~r1_relat_2(u1_orders_2('#skF_8'), u1_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_1130])).
% 3.59/1.61  tff(c_1142, plain, (~v3_orders_2('#skF_8') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_54, c_1136])).
% 3.59/1.61  tff(c_1146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_80, c_1142])).
% 3.59/1.61  tff(c_1147, plain, (~m1_subset_1(k6_domain_1(u1_struct_0('#skF_8'), '#skF_9'), k1_zfmisc_1(u1_struct_0('#skF_8')))), inference(splitRight, [status(thm)], [c_74])).
% 3.59/1.61  tff(c_1203, plain, (~m1_subset_1(k1_tarski('#skF_9'), k1_zfmisc_1(u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_1201, c_1147])).
% 3.59/1.61  tff(c_1283, plain, (![A_2144, B_2145]: (m1_subset_1(k6_domain_1(A_2144, B_2145), k1_zfmisc_1(A_2144)) | ~m1_subset_1(B_2145, A_2144) | v1_xboole_0(A_2144))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.59/1.61  tff(c_1292, plain, (m1_subset_1(k1_tarski('#skF_9'), k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | v1_xboole_0(u1_struct_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1201, c_1283])).
% 3.59/1.61  tff(c_1296, plain, (m1_subset_1(k1_tarski('#skF_9'), k1_zfmisc_1(u1_struct_0('#skF_8'))) | v1_xboole_0(u1_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1292])).
% 3.59/1.61  tff(c_1298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1202, c_1203, c_1296])).
% 3.59/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.61  
% 3.59/1.61  Inference rules
% 3.59/1.61  ----------------------
% 3.59/1.61  #Ref     : 0
% 3.59/1.61  #Sup     : 252
% 3.59/1.61  #Fact    : 0
% 3.59/1.61  #Define  : 0
% 3.59/1.61  #Split   : 8
% 3.59/1.61  #Chain   : 0
% 3.59/1.61  #Close   : 0
% 3.59/1.61  
% 3.59/1.61  Ordering : KBO
% 3.59/1.61  
% 3.59/1.61  Simplification rules
% 3.59/1.61  ----------------------
% 3.59/1.61  #Subsume      : 16
% 3.59/1.61  #Demod        : 41
% 3.59/1.61  #Tautology    : 27
% 3.59/1.61  #SimpNegUnit  : 12
% 3.59/1.61  #BackRed      : 3
% 3.59/1.61  
% 3.59/1.61  #Partial instantiations: 1156
% 3.59/1.61  #Strategies tried      : 1
% 3.59/1.61  
% 3.59/1.61  Timing (in seconds)
% 3.59/1.61  ----------------------
% 3.59/1.61  Preprocessing        : 0.36
% 3.59/1.61  Parsing              : 0.18
% 3.59/1.61  CNF conversion       : 0.03
% 3.59/1.61  Main loop            : 0.47
% 3.59/1.61  Inferencing          : 0.19
% 3.59/1.61  Reduction            : 0.13
% 3.59/1.61  Demodulation         : 0.09
% 3.59/1.61  BG Simplification    : 0.03
% 3.59/1.61  Subsumption          : 0.08
% 3.59/1.61  Abstraction          : 0.03
% 3.59/1.61  MUC search           : 0.00
% 3.59/1.61  Cooper               : 0.00
% 3.59/1.61  Total                : 0.87
% 3.59/1.61  Index Insertion      : 0.00
% 3.59/1.61  Index Deletion       : 0.00
% 3.59/1.61  Index Matching       : 0.00
% 3.59/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
