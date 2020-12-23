%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1625+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:08 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 362 expanded)
%              Number of leaves         :   38 ( 136 expanded)
%              Depth                    :   15
%              Number of atoms          :  273 (1010 expanded)
%              Number of equality atoms :   14 (  92 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > v2_waybel_0 > v1_waybel_0 > r2_hidden > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_10 > #skF_6 > #skF_8 > #skF_9 > #skF_2 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

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

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(v1_waybel_0,type,(
    v1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_waybel_0(k6_domain_1(u1_struct_0(A),B),A)
              & v2_waybel_0(k6_domain_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_waybel_0)).

tff(f_141,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ~ ( r2_hidden(C,B)
                        & r2_hidden(D,B)
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(A))
                           => ~ ( r2_hidden(E,B)
                                & r1_orders_2(A,C,E)
                                & r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_waybel_0)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ~ ( r2_hidden(C,B)
                        & r2_hidden(D,B)
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(A))
                           => ~ ( r2_hidden(E,B)
                                & r1_orders_2(A,E,C)
                                & r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_waybel_0)).

tff(c_68,plain,(
    m1_subset_1('#skF_10',u1_struct_0('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_72,plain,(
    v3_orders_2('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_70,plain,(
    l1_orders_2('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_887,plain,(
    ! [A_244,B_245,C_246] :
      ( r3_orders_2(A_244,B_245,B_245)
      | ~ m1_subset_1(C_246,u1_struct_0(A_244))
      | ~ m1_subset_1(B_245,u1_struct_0(A_244))
      | ~ l1_orders_2(A_244)
      | ~ v3_orders_2(A_244)
      | v2_struct_0(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_899,plain,(
    ! [B_245] :
      ( r3_orders_2('#skF_9',B_245,B_245)
      | ~ m1_subset_1(B_245,u1_struct_0('#skF_9'))
      | ~ l1_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_68,c_887])).

tff(c_910,plain,(
    ! [B_245] :
      ( r3_orders_2('#skF_9',B_245,B_245)
      | ~ m1_subset_1(B_245,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_899])).

tff(c_912,plain,(
    ! [B_247] :
      ( r3_orders_2('#skF_9',B_247,B_247)
      | ~ m1_subset_1(B_247,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_910])).

tff(c_942,plain,(
    r3_orders_2('#skF_9','#skF_10','#skF_10') ),
    inference(resolution,[status(thm)],[c_68,c_912])).

tff(c_1004,plain,(
    ! [A_255,B_256,C_257] :
      ( r1_orders_2(A_255,B_256,C_257)
      | ~ r3_orders_2(A_255,B_256,C_257)
      | ~ m1_subset_1(C_257,u1_struct_0(A_255))
      | ~ m1_subset_1(B_256,u1_struct_0(A_255))
      | ~ l1_orders_2(A_255)
      | ~ v3_orders_2(A_255)
      | v2_struct_0(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1014,plain,
    ( r1_orders_2('#skF_9','#skF_10','#skF_10')
    | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_9'))
    | ~ l1_orders_2('#skF_9')
    | ~ v3_orders_2('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_942,c_1004])).

tff(c_1033,plain,
    ( r1_orders_2('#skF_9','#skF_10','#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1014])).

tff(c_1034,plain,(
    r1_orders_2('#skF_9','#skF_10','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1033])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ! [A_120] :
      ( l1_struct_0(A_120)
      | ~ l1_orders_2(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_628,plain,(
    ! [A_206,B_207] :
      ( k6_domain_1(A_206,B_207) = k1_tarski(B_207)
      | ~ m1_subset_1(B_207,A_206)
      | v1_xboole_0(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_632,plain,
    ( k6_domain_1(u1_struct_0('#skF_9'),'#skF_10') = k1_tarski('#skF_10')
    | v1_xboole_0(u1_struct_0('#skF_9')) ),
    inference(resolution,[status(thm)],[c_68,c_628])).

tff(c_633,plain,(
    v1_xboole_0(u1_struct_0('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_632])).

tff(c_54,plain,(
    ! [A_121] :
      ( ~ v1_xboole_0(u1_struct_0(A_121))
      | ~ l1_struct_0(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_636,plain,
    ( ~ l1_struct_0('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_633,c_54])).

tff(c_639,plain,(
    ~ l1_struct_0('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_636])).

tff(c_642,plain,(
    ~ l1_orders_2('#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_639])).

tff(c_646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_642])).

tff(c_647,plain,(
    k6_domain_1(u1_struct_0('#skF_9'),'#skF_10') = k1_tarski('#skF_10') ),
    inference(splitRight,[status(thm)],[c_632])).

tff(c_310,plain,(
    ! [A_176,B_177,C_178] :
      ( r3_orders_2(A_176,B_177,B_177)
      | ~ m1_subset_1(C_178,u1_struct_0(A_176))
      | ~ m1_subset_1(B_177,u1_struct_0(A_176))
      | ~ l1_orders_2(A_176)
      | ~ v3_orders_2(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_320,plain,(
    ! [B_177] :
      ( r3_orders_2('#skF_9',B_177,B_177)
      | ~ m1_subset_1(B_177,u1_struct_0('#skF_9'))
      | ~ l1_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_68,c_310])).

tff(c_327,plain,(
    ! [B_177] :
      ( r3_orders_2('#skF_9',B_177,B_177)
      | ~ m1_subset_1(B_177,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_320])).

tff(c_329,plain,(
    ! [B_179] :
      ( r3_orders_2('#skF_9',B_179,B_179)
      | ~ m1_subset_1(B_179,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_327])).

tff(c_356,plain,(
    r3_orders_2('#skF_9','#skF_10','#skF_10') ),
    inference(resolution,[status(thm)],[c_68,c_329])).

tff(c_434,plain,(
    ! [A_189,B_190,C_191] :
      ( r1_orders_2(A_189,B_190,C_191)
      | ~ r3_orders_2(A_189,B_190,C_191)
      | ~ m1_subset_1(C_191,u1_struct_0(A_189))
      | ~ m1_subset_1(B_190,u1_struct_0(A_189))
      | ~ l1_orders_2(A_189)
      | ~ v3_orders_2(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_444,plain,
    ( r1_orders_2('#skF_9','#skF_10','#skF_10')
    | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_9'))
    | ~ l1_orders_2('#skF_9')
    | ~ v3_orders_2('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_356,c_434])).

tff(c_463,plain,
    ( r1_orders_2('#skF_9','#skF_10','#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_444])).

tff(c_464,plain,(
    r1_orders_2('#skF_9','#skF_10','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_463])).

tff(c_86,plain,(
    ! [A_142,B_143] :
      ( k6_domain_1(A_142,B_143) = k1_tarski(B_143)
      | ~ m1_subset_1(B_143,A_142)
      | v1_xboole_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_90,plain,
    ( k6_domain_1(u1_struct_0('#skF_9'),'#skF_10') = k1_tarski('#skF_10')
    | v1_xboole_0(u1_struct_0('#skF_9')) ),
    inference(resolution,[status(thm)],[c_68,c_86])).

tff(c_91,plain,(
    v1_xboole_0(u1_struct_0('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_94,plain,
    ( ~ l1_struct_0('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_91,c_54])).

tff(c_97,plain,(
    ~ l1_struct_0('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_94])).

tff(c_100,plain,(
    ~ l1_orders_2('#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_97])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_100])).

tff(c_105,plain,(
    k6_domain_1(u1_struct_0('#skF_9'),'#skF_10') = k1_tarski('#skF_10') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_66,plain,
    ( ~ v2_waybel_0(k6_domain_1(u1_struct_0('#skF_9'),'#skF_10'),'#skF_9')
    | ~ v1_waybel_0(k6_domain_1(u1_struct_0('#skF_9'),'#skF_10'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_85,plain,(
    ~ v1_waybel_0(k6_domain_1(u1_struct_0('#skF_9'),'#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_115,plain,(
    ~ v1_waybel_0(k1_tarski('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_85])).

tff(c_106,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_50,plain,(
    ! [A_118,B_119] :
      ( m1_subset_1(k6_domain_1(A_118,B_119),k1_zfmisc_1(A_118))
      | ~ m1_subset_1(B_119,A_118)
      | v1_xboole_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_119,plain,
    ( m1_subset_1(k1_tarski('#skF_10'),k1_zfmisc_1(u1_struct_0('#skF_9')))
    | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_9'))
    | v1_xboole_0(u1_struct_0('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_50])).

tff(c_123,plain,
    ( m1_subset_1(k1_tarski('#skF_10'),k1_zfmisc_1(u1_struct_0('#skF_9')))
    | v1_xboole_0(u1_struct_0('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_119])).

tff(c_124,plain,(
    m1_subset_1(k1_tarski('#skF_10'),k1_zfmisc_1(u1_struct_0('#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_123])).

tff(c_245,plain,(
    ! [A_166,B_167] :
      ( r2_hidden('#skF_4'(A_166,B_167),B_167)
      | v1_waybel_0(B_167,A_166)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_orders_2(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_247,plain,
    ( r2_hidden('#skF_4'('#skF_9',k1_tarski('#skF_10')),k1_tarski('#skF_10'))
    | v1_waybel_0(k1_tarski('#skF_10'),'#skF_9')
    | ~ l1_orders_2('#skF_9') ),
    inference(resolution,[status(thm)],[c_124,c_245])).

tff(c_253,plain,
    ( r2_hidden('#skF_4'('#skF_9',k1_tarski('#skF_10')),k1_tarski('#skF_10'))
    | v1_waybel_0(k1_tarski('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_247])).

tff(c_254,plain,(
    r2_hidden('#skF_4'('#skF_9',k1_tarski('#skF_10')),k1_tarski('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_253])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_269,plain,(
    '#skF_4'('#skF_9',k1_tarski('#skF_10')) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_254,c_2])).

tff(c_226,plain,(
    ! [A_164,B_165] :
      ( r2_hidden('#skF_5'(A_164,B_165),B_165)
      | v1_waybel_0(B_165,A_164)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_orders_2(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_228,plain,
    ( r2_hidden('#skF_5'('#skF_9',k1_tarski('#skF_10')),k1_tarski('#skF_10'))
    | v1_waybel_0(k1_tarski('#skF_10'),'#skF_9')
    | ~ l1_orders_2('#skF_9') ),
    inference(resolution,[status(thm)],[c_124,c_226])).

tff(c_234,plain,
    ( r2_hidden('#skF_5'('#skF_9',k1_tarski('#skF_10')),k1_tarski('#skF_10'))
    | v1_waybel_0(k1_tarski('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_228])).

tff(c_235,plain,(
    r2_hidden('#skF_5'('#skF_9',k1_tarski('#skF_10')),k1_tarski('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_234])).

tff(c_244,plain,(
    '#skF_5'('#skF_9',k1_tarski('#skF_10')) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_235,c_2])).

tff(c_601,plain,(
    ! [A_202,B_203,E_204] :
      ( ~ r1_orders_2(A_202,'#skF_5'(A_202,B_203),E_204)
      | ~ r1_orders_2(A_202,'#skF_4'(A_202,B_203),E_204)
      | ~ r2_hidden(E_204,B_203)
      | ~ m1_subset_1(E_204,u1_struct_0(A_202))
      | v1_waybel_0(B_203,A_202)
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_orders_2(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_603,plain,(
    ! [E_204] :
      ( ~ r1_orders_2('#skF_9','#skF_10',E_204)
      | ~ r1_orders_2('#skF_9','#skF_4'('#skF_9',k1_tarski('#skF_10')),E_204)
      | ~ r2_hidden(E_204,k1_tarski('#skF_10'))
      | ~ m1_subset_1(E_204,u1_struct_0('#skF_9'))
      | v1_waybel_0(k1_tarski('#skF_10'),'#skF_9')
      | ~ m1_subset_1(k1_tarski('#skF_10'),k1_zfmisc_1(u1_struct_0('#skF_9')))
      | ~ l1_orders_2('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_601])).

tff(c_605,plain,(
    ! [E_204] :
      ( ~ r1_orders_2('#skF_9','#skF_10',E_204)
      | ~ r2_hidden(E_204,k1_tarski('#skF_10'))
      | ~ m1_subset_1(E_204,u1_struct_0('#skF_9'))
      | v1_waybel_0(k1_tarski('#skF_10'),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_124,c_269,c_603])).

tff(c_607,plain,(
    ! [E_205] :
      ( ~ r1_orders_2('#skF_9','#skF_10',E_205)
      | ~ r2_hidden(E_205,k1_tarski('#skF_10'))
      | ~ m1_subset_1(E_205,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_605])).

tff(c_619,plain,
    ( ~ r1_orders_2('#skF_9','#skF_10','#skF_10')
    | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_9')) ),
    inference(resolution,[status(thm)],[c_4,c_607])).

tff(c_625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_464,c_619])).

tff(c_626,plain,(
    ~ v2_waybel_0(k6_domain_1(u1_struct_0('#skF_9'),'#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_650,plain,(
    ~ v2_waybel_0(k1_tarski('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_626])).

tff(c_648,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_632])).

tff(c_655,plain,(
    ! [A_208,B_209] :
      ( m1_subset_1(k6_domain_1(A_208,B_209),k1_zfmisc_1(A_208))
      | ~ m1_subset_1(B_209,A_208)
      | v1_xboole_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_663,plain,
    ( m1_subset_1(k1_tarski('#skF_10'),k1_zfmisc_1(u1_struct_0('#skF_9')))
    | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_9'))
    | v1_xboole_0(u1_struct_0('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_655])).

tff(c_667,plain,
    ( m1_subset_1(k1_tarski('#skF_10'),k1_zfmisc_1(u1_struct_0('#skF_9')))
    | v1_xboole_0(u1_struct_0('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_663])).

tff(c_668,plain,(
    m1_subset_1(k1_tarski('#skF_10'),k1_zfmisc_1(u1_struct_0('#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_648,c_667])).

tff(c_780,plain,(
    ! [A_229,B_230] :
      ( r2_hidden('#skF_7'(A_229,B_230),B_230)
      | v2_waybel_0(B_230,A_229)
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ l1_orders_2(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_782,plain,
    ( r2_hidden('#skF_7'('#skF_9',k1_tarski('#skF_10')),k1_tarski('#skF_10'))
    | v2_waybel_0(k1_tarski('#skF_10'),'#skF_9')
    | ~ l1_orders_2('#skF_9') ),
    inference(resolution,[status(thm)],[c_668,c_780])).

tff(c_788,plain,
    ( r2_hidden('#skF_7'('#skF_9',k1_tarski('#skF_10')),k1_tarski('#skF_10'))
    | v2_waybel_0(k1_tarski('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_782])).

tff(c_789,plain,(
    r2_hidden('#skF_7'('#skF_9',k1_tarski('#skF_10')),k1_tarski('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_650,c_788])).

tff(c_798,plain,(
    '#skF_7'('#skF_9',k1_tarski('#skF_10')) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_789,c_2])).

tff(c_806,plain,(
    ! [A_231,B_232] :
      ( r2_hidden('#skF_8'(A_231,B_232),B_232)
      | v2_waybel_0(B_232,A_231)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ l1_orders_2(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_808,plain,
    ( r2_hidden('#skF_8'('#skF_9',k1_tarski('#skF_10')),k1_tarski('#skF_10'))
    | v2_waybel_0(k1_tarski('#skF_10'),'#skF_9')
    | ~ l1_orders_2('#skF_9') ),
    inference(resolution,[status(thm)],[c_668,c_806])).

tff(c_814,plain,
    ( r2_hidden('#skF_8'('#skF_9',k1_tarski('#skF_10')),k1_tarski('#skF_10'))
    | v2_waybel_0(k1_tarski('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_808])).

tff(c_815,plain,(
    r2_hidden('#skF_8'('#skF_9',k1_tarski('#skF_10')),k1_tarski('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_650,c_814])).

tff(c_824,plain,(
    '#skF_8'('#skF_9',k1_tarski('#skF_10')) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_815,c_2])).

tff(c_1276,plain,(
    ! [A_284,E_285,B_286] :
      ( ~ r1_orders_2(A_284,E_285,'#skF_8'(A_284,B_286))
      | ~ r1_orders_2(A_284,E_285,'#skF_7'(A_284,B_286))
      | ~ r2_hidden(E_285,B_286)
      | ~ m1_subset_1(E_285,u1_struct_0(A_284))
      | v2_waybel_0(B_286,A_284)
      | ~ m1_subset_1(B_286,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ l1_orders_2(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1280,plain,(
    ! [E_285] :
      ( ~ r1_orders_2('#skF_9',E_285,'#skF_10')
      | ~ r1_orders_2('#skF_9',E_285,'#skF_7'('#skF_9',k1_tarski('#skF_10')))
      | ~ r2_hidden(E_285,k1_tarski('#skF_10'))
      | ~ m1_subset_1(E_285,u1_struct_0('#skF_9'))
      | v2_waybel_0(k1_tarski('#skF_10'),'#skF_9')
      | ~ m1_subset_1(k1_tarski('#skF_10'),k1_zfmisc_1(u1_struct_0('#skF_9')))
      | ~ l1_orders_2('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_824,c_1276])).

tff(c_1285,plain,(
    ! [E_285] :
      ( ~ r1_orders_2('#skF_9',E_285,'#skF_10')
      | ~ r2_hidden(E_285,k1_tarski('#skF_10'))
      | ~ m1_subset_1(E_285,u1_struct_0('#skF_9'))
      | v2_waybel_0(k1_tarski('#skF_10'),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_668,c_798,c_1280])).

tff(c_1287,plain,(
    ! [E_287] :
      ( ~ r1_orders_2('#skF_9',E_287,'#skF_10')
      | ~ r2_hidden(E_287,k1_tarski('#skF_10'))
      | ~ m1_subset_1(E_287,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_650,c_1285])).

tff(c_1299,plain,
    ( ~ r1_orders_2('#skF_9','#skF_10','#skF_10')
    | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_9')) ),
    inference(resolution,[status(thm)],[c_4,c_1287])).

tff(c_1305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1034,c_1299])).

%------------------------------------------------------------------------------
