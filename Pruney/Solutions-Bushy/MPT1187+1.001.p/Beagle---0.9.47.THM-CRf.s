%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1187+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:33 EST 2020

% Result     : Theorem 6.12s
% Output     : CNFRefutation 6.32s
% Verified   : 
% Statistics : Number of formulae       :  179 (1090 expanded)
%              Number of leaves         :   47 ( 406 expanded)
%              Depth                    :   24
%              Number of atoms          :  533 (4595 expanded)
%              Number of equality atoms :   49 ( 249 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > v1_partfun1 > r6_orders_1 > r2_hidden > m1_subset_1 > v8_relat_2 > v5_orders_2 > v4_relat_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_orders_2 > v1_xboole_0 > v1_relat_2 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_orders_2,type,(
    v2_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r6_orders_1,type,(
    r6_orders_1: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_166,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( r6_orders_1(u1_orders_2(A),B)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ r2_orders_2(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_orders_2)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_143,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_orders_2(A)
       => v2_orders_2(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_orders_2)).

tff(f_105,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & l1_orders_2(A) )
     => v1_relat_2(u1_orders_2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_orders_2)).

tff(f_113,axiom,(
    ! [A] :
      ( ( v2_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => v4_relat_2(u1_orders_2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_orders_2)).

tff(f_121,axiom,(
    ! [A] :
      ( ( v2_orders_2(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => v8_relat_2(u1_orders_2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_orders_2)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v2_orders_2(A)
        & l1_orders_2(A) )
     => v1_partfun1(u1_orders_2(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_orders_2)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( v1_relat_2(B)
        & v4_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k3_relat_1(B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_orders_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r6_orders_1(A,B)
        <=> ( r2_hidden(B,k3_relat_1(A))
            & ! [C] :
                ~ ( r2_hidden(C,k3_relat_1(A))
                  & C != B
                  & r2_hidden(k4_tarski(B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_1)).

tff(f_137,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_49,axiom,(
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

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_48,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_26,plain,(
    ! [A_29] :
      ( l1_struct_0(A_29)
      | ~ l1_orders_2(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_44,plain,(
    ! [A_40,B_41] :
      ( r2_hidden(A_40,B_41)
      | v1_xboole_0(B_41)
      | ~ m1_subset_1(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_54,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_71,plain,(
    ! [A_53] :
      ( v2_orders_2(A_53)
      | ~ v3_orders_2(A_53)
      | ~ l1_orders_2(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_74,plain,
    ( v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_71])).

tff(c_77,plain,(
    v2_orders_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_74])).

tff(c_50,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_52,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_34,plain,(
    ! [A_33] :
      ( v1_relat_2(u1_orders_2(A_33))
      | ~ l1_orders_2(A_33)
      | ~ v3_orders_2(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36,plain,(
    ! [A_34] :
      ( v4_relat_2(u1_orders_2(A_34))
      | ~ l1_orders_2(A_34)
      | ~ v5_orders_2(A_34)
      | ~ v2_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_38,plain,(
    ! [A_35] :
      ( v8_relat_2(u1_orders_2(A_35))
      | ~ l1_orders_2(A_35)
      | ~ v4_orders_2(A_35)
      | ~ v2_orders_2(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_30,plain,(
    ! [A_31] :
      ( v1_partfun1(u1_orders_2(A_31),u1_struct_0(A_31))
      | ~ l1_orders_2(A_31)
      | ~ v2_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    ! [A_30] :
      ( m1_subset_1(u1_orders_2(A_30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_30),u1_struct_0(A_30))))
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_987,plain,(
    ! [B_265,A_266] :
      ( k3_relat_1(B_265) = A_266
      | ~ m1_subset_1(B_265,k1_zfmisc_1(k2_zfmisc_1(A_266,A_266)))
      | ~ v1_partfun1(B_265,A_266)
      | ~ v8_relat_2(B_265)
      | ~ v4_relat_2(B_265)
      | ~ v1_relat_2(B_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1097,plain,(
    ! [A_291] :
      ( k3_relat_1(u1_orders_2(A_291)) = u1_struct_0(A_291)
      | ~ v1_partfun1(u1_orders_2(A_291),u1_struct_0(A_291))
      | ~ v8_relat_2(u1_orders_2(A_291))
      | ~ v4_relat_2(u1_orders_2(A_291))
      | ~ v1_relat_2(u1_orders_2(A_291))
      | ~ l1_orders_2(A_291) ) ),
    inference(resolution,[status(thm)],[c_28,c_987])).

tff(c_1102,plain,(
    ! [A_292] :
      ( k3_relat_1(u1_orders_2(A_292)) = u1_struct_0(A_292)
      | ~ v8_relat_2(u1_orders_2(A_292))
      | ~ v4_relat_2(u1_orders_2(A_292))
      | ~ v1_relat_2(u1_orders_2(A_292))
      | ~ l1_orders_2(A_292)
      | ~ v2_orders_2(A_292) ) ),
    inference(resolution,[status(thm)],[c_30,c_1097])).

tff(c_1107,plain,(
    ! [A_293] :
      ( k3_relat_1(u1_orders_2(A_293)) = u1_struct_0(A_293)
      | ~ v4_relat_2(u1_orders_2(A_293))
      | ~ v1_relat_2(u1_orders_2(A_293))
      | ~ l1_orders_2(A_293)
      | ~ v4_orders_2(A_293)
      | ~ v2_orders_2(A_293) ) ),
    inference(resolution,[status(thm)],[c_38,c_1102])).

tff(c_1112,plain,(
    ! [A_294] :
      ( k3_relat_1(u1_orders_2(A_294)) = u1_struct_0(A_294)
      | ~ v1_relat_2(u1_orders_2(A_294))
      | ~ v4_orders_2(A_294)
      | ~ l1_orders_2(A_294)
      | ~ v5_orders_2(A_294)
      | ~ v2_orders_2(A_294) ) ),
    inference(resolution,[status(thm)],[c_36,c_1107])).

tff(c_1116,plain,(
    ! [A_33] :
      ( k3_relat_1(u1_orders_2(A_33)) = u1_struct_0(A_33)
      | ~ v4_orders_2(A_33)
      | ~ v5_orders_2(A_33)
      | ~ v2_orders_2(A_33)
      | ~ l1_orders_2(A_33)
      | ~ v3_orders_2(A_33) ) ),
    inference(resolution,[status(thm)],[c_34,c_1112])).

tff(c_60,plain,
    ( m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ r6_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_78,plain,(
    ~ r6_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_927,plain,(
    ! [A_250] :
      ( m1_subset_1(u1_orders_2(A_250),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_250),u1_struct_0(A_250))))
      | ~ l1_orders_2(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4,plain,(
    ! [C_4,A_2,B_3] :
      ( v1_relat_1(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(A_2,B_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_931,plain,(
    ! [A_250] :
      ( v1_relat_1(u1_orders_2(A_250))
      | ~ l1_orders_2(A_250) ) ),
    inference(resolution,[status(thm)],[c_927,c_4])).

tff(c_1117,plain,(
    ! [A_295] :
      ( k3_relat_1(u1_orders_2(A_295)) = u1_struct_0(A_295)
      | ~ v4_orders_2(A_295)
      | ~ v5_orders_2(A_295)
      | ~ v2_orders_2(A_295)
      | ~ l1_orders_2(A_295)
      | ~ v3_orders_2(A_295) ) ),
    inference(resolution,[status(thm)],[c_34,c_1112])).

tff(c_18,plain,(
    ! [A_12,B_18] :
      ( '#skF_1'(A_12,B_18) != B_18
      | r6_orders_1(A_12,B_18)
      | ~ r2_hidden(B_18,k3_relat_1(A_12))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1250,plain,(
    ! [A_323,B_324] :
      ( '#skF_1'(u1_orders_2(A_323),B_324) != B_324
      | r6_orders_1(u1_orders_2(A_323),B_324)
      | ~ r2_hidden(B_324,u1_struct_0(A_323))
      | ~ v1_relat_1(u1_orders_2(A_323))
      | ~ v4_orders_2(A_323)
      | ~ v5_orders_2(A_323)
      | ~ v2_orders_2(A_323)
      | ~ l1_orders_2(A_323)
      | ~ v3_orders_2(A_323) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1117,c_18])).

tff(c_1259,plain,
    ( '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') != '#skF_3'
    | ~ r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_1250,c_78])).

tff(c_1264,plain,
    ( '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') != '#skF_3'
    | ~ r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_77,c_50,c_52,c_1259])).

tff(c_1265,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1264])).

tff(c_1268,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_931,c_1265])).

tff(c_1272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1268])).

tff(c_1273,plain,
    ( ~ r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1264])).

tff(c_1275,plain,(
    '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1273])).

tff(c_1274,plain,(
    v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1264])).

tff(c_943,plain,(
    ! [A_254,B_255] :
      ( r2_hidden('#skF_1'(A_254,B_255),k3_relat_1(A_254))
      | r6_orders_1(A_254,B_255)
      | ~ r2_hidden(B_255,k3_relat_1(A_254))
      | ~ v1_relat_1(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(A_38,B_39)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_951,plain,(
    ! [A_254,B_255] :
      ( m1_subset_1('#skF_1'(A_254,B_255),k3_relat_1(A_254))
      | r6_orders_1(A_254,B_255)
      | ~ r2_hidden(B_255,k3_relat_1(A_254))
      | ~ v1_relat_1(A_254) ) ),
    inference(resolution,[status(thm)],[c_943,c_42])).

tff(c_1286,plain,(
    ! [A_333,B_334] :
      ( m1_subset_1('#skF_1'(u1_orders_2(A_333),B_334),u1_struct_0(A_333))
      | r6_orders_1(u1_orders_2(A_333),B_334)
      | ~ r2_hidden(B_334,k3_relat_1(u1_orders_2(A_333)))
      | ~ v1_relat_1(u1_orders_2(A_333))
      | ~ v4_orders_2(A_333)
      | ~ v5_orders_2(A_333)
      | ~ v2_orders_2(A_333)
      | ~ l1_orders_2(A_333)
      | ~ v3_orders_2(A_333) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1117,c_951])).

tff(c_16,plain,(
    ! [B_18,A_12] :
      ( r2_hidden(k4_tarski(B_18,'#skF_1'(A_12,B_18)),A_12)
      | r6_orders_1(A_12,B_18)
      | ~ r2_hidden(B_18,k3_relat_1(A_12))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1078,plain,(
    ! [A_285,B_286,C_287] :
      ( r1_orders_2(A_285,B_286,C_287)
      | ~ r2_hidden(k4_tarski(B_286,C_287),u1_orders_2(A_285))
      | ~ m1_subset_1(C_287,u1_struct_0(A_285))
      | ~ m1_subset_1(B_286,u1_struct_0(A_285))
      | ~ l1_orders_2(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1090,plain,(
    ! [A_285,B_18] :
      ( r1_orders_2(A_285,B_18,'#skF_1'(u1_orders_2(A_285),B_18))
      | ~ m1_subset_1('#skF_1'(u1_orders_2(A_285),B_18),u1_struct_0(A_285))
      | ~ m1_subset_1(B_18,u1_struct_0(A_285))
      | ~ l1_orders_2(A_285)
      | r6_orders_1(u1_orders_2(A_285),B_18)
      | ~ r2_hidden(B_18,k3_relat_1(u1_orders_2(A_285)))
      | ~ v1_relat_1(u1_orders_2(A_285)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1078])).

tff(c_1299,plain,(
    ! [A_333,B_334] :
      ( r1_orders_2(A_333,B_334,'#skF_1'(u1_orders_2(A_333),B_334))
      | ~ m1_subset_1(B_334,u1_struct_0(A_333))
      | r6_orders_1(u1_orders_2(A_333),B_334)
      | ~ r2_hidden(B_334,k3_relat_1(u1_orders_2(A_333)))
      | ~ v1_relat_1(u1_orders_2(A_333))
      | ~ v4_orders_2(A_333)
      | ~ v5_orders_2(A_333)
      | ~ v2_orders_2(A_333)
      | ~ l1_orders_2(A_333)
      | ~ v3_orders_2(A_333) ) ),
    inference(resolution,[status(thm)],[c_1286,c_1090])).

tff(c_6,plain,(
    ! [A_5,B_9,C_11] :
      ( r2_orders_2(A_5,B_9,C_11)
      | C_11 = B_9
      | ~ r1_orders_2(A_5,B_9,C_11)
      | ~ m1_subset_1(C_11,u1_struct_0(A_5))
      | ~ m1_subset_1(B_9,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1659,plain,(
    ! [A_415,B_416,B_417] :
      ( r2_orders_2(A_415,B_416,'#skF_1'(u1_orders_2(A_415),B_417))
      | B_416 = '#skF_1'(u1_orders_2(A_415),B_417)
      | ~ r1_orders_2(A_415,B_416,'#skF_1'(u1_orders_2(A_415),B_417))
      | ~ m1_subset_1(B_416,u1_struct_0(A_415))
      | r6_orders_1(u1_orders_2(A_415),B_417)
      | ~ r2_hidden(B_417,k3_relat_1(u1_orders_2(A_415)))
      | ~ v1_relat_1(u1_orders_2(A_415))
      | ~ v4_orders_2(A_415)
      | ~ v5_orders_2(A_415)
      | ~ v2_orders_2(A_415)
      | ~ l1_orders_2(A_415)
      | ~ v3_orders_2(A_415) ) ),
    inference(resolution,[status(thm)],[c_1286,c_6])).

tff(c_68,plain,(
    ! [C_49] :
      ( r6_orders_1(u1_orders_2('#skF_2'),'#skF_3')
      | ~ r2_orders_2('#skF_2','#skF_3',C_49)
      | ~ m1_subset_1(C_49,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_913,plain,(
    ! [C_49] :
      ( ~ r2_orders_2('#skF_2','#skF_3',C_49)
      | ~ m1_subset_1(C_49,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_68])).

tff(c_1298,plain,(
    ! [B_334] :
      ( ~ r2_orders_2('#skF_2','#skF_3','#skF_1'(u1_orders_2('#skF_2'),B_334))
      | r6_orders_1(u1_orders_2('#skF_2'),B_334)
      | ~ r2_hidden(B_334,k3_relat_1(u1_orders_2('#skF_2')))
      | ~ v1_relat_1(u1_orders_2('#skF_2'))
      | ~ v4_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v2_orders_2('#skF_2')
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1286,c_913])).

tff(c_1306,plain,(
    ! [B_334] :
      ( ~ r2_orders_2('#skF_2','#skF_3','#skF_1'(u1_orders_2('#skF_2'),B_334))
      | r6_orders_1(u1_orders_2('#skF_2'),B_334)
      | ~ r2_hidden(B_334,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_77,c_50,c_52,c_1274,c_1298])).

tff(c_1663,plain,(
    ! [B_417] :
      ( '#skF_1'(u1_orders_2('#skF_2'),B_417) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_orders_2('#skF_2'),B_417))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | r6_orders_1(u1_orders_2('#skF_2'),B_417)
      | ~ r2_hidden(B_417,k3_relat_1(u1_orders_2('#skF_2')))
      | ~ v1_relat_1(u1_orders_2('#skF_2'))
      | ~ v4_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v2_orders_2('#skF_2')
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1659,c_1306])).

tff(c_1675,plain,(
    ! [B_418] :
      ( '#skF_1'(u1_orders_2('#skF_2'),B_418) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_orders_2('#skF_2'),B_418))
      | r6_orders_1(u1_orders_2('#skF_2'),B_418)
      | ~ r2_hidden(B_418,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_77,c_50,c_52,c_1274,c_46,c_1663])).

tff(c_1679,plain,
    ( '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | r6_orders_1(u1_orders_2('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_3',k3_relat_1(u1_orders_2('#skF_2')))
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_1299,c_1675])).

tff(c_1682,plain,
    ( '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') = '#skF_3'
    | r6_orders_1(u1_orders_2('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_3',k3_relat_1(u1_orders_2('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_77,c_50,c_52,c_1274,c_46,c_1679])).

tff(c_1683,plain,(
    ~ r2_hidden('#skF_3',k3_relat_1(u1_orders_2('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1275,c_1682])).

tff(c_1686,plain,
    ( ~ r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1116,c_1683])).

tff(c_1694,plain,(
    ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_77,c_50,c_52,c_1686])).

tff(c_1702,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_1694])).

tff(c_1705,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1702])).

tff(c_32,plain,(
    ! [A_32] :
      ( ~ v1_xboole_0(u1_struct_0(A_32))
      | ~ l1_struct_0(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1708,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1705,c_32])).

tff(c_1711,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1708])).

tff(c_1714,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_1711])).

tff(c_1718,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1714])).

tff(c_1719,plain,(
    ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1273])).

tff(c_1724,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_1719])).

tff(c_1727,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1724])).

tff(c_1730,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1727,c_32])).

tff(c_1733,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1730])).

tff(c_1736,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_1733])).

tff(c_1740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1736])).

tff(c_1741,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1742,plain,(
    r6_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ r6_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1743,plain,(
    ~ r6_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_1745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1742,c_1743])).

tff(c_1746,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1851,plain,(
    ! [A_456,B_457,C_458] :
      ( r1_orders_2(A_456,B_457,C_458)
      | ~ r2_orders_2(A_456,B_457,C_458)
      | ~ m1_subset_1(C_458,u1_struct_0(A_456))
      | ~ m1_subset_1(B_457,u1_struct_0(A_456))
      | ~ l1_orders_2(A_456) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1853,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_1746,c_1851])).

tff(c_1856,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1741,c_1853])).

tff(c_1821,plain,(
    ! [B_450,A_451] :
      ( k3_relat_1(B_450) = A_451
      | ~ m1_subset_1(B_450,k1_zfmisc_1(k2_zfmisc_1(A_451,A_451)))
      | ~ v1_partfun1(B_450,A_451)
      | ~ v8_relat_2(B_450)
      | ~ v4_relat_2(B_450)
      | ~ v1_relat_2(B_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1975,plain,(
    ! [A_482] :
      ( k3_relat_1(u1_orders_2(A_482)) = u1_struct_0(A_482)
      | ~ v1_partfun1(u1_orders_2(A_482),u1_struct_0(A_482))
      | ~ v8_relat_2(u1_orders_2(A_482))
      | ~ v4_relat_2(u1_orders_2(A_482))
      | ~ v1_relat_2(u1_orders_2(A_482))
      | ~ l1_orders_2(A_482) ) ),
    inference(resolution,[status(thm)],[c_28,c_1821])).

tff(c_1980,plain,(
    ! [A_483] :
      ( k3_relat_1(u1_orders_2(A_483)) = u1_struct_0(A_483)
      | ~ v8_relat_2(u1_orders_2(A_483))
      | ~ v4_relat_2(u1_orders_2(A_483))
      | ~ v1_relat_2(u1_orders_2(A_483))
      | ~ l1_orders_2(A_483)
      | ~ v2_orders_2(A_483) ) ),
    inference(resolution,[status(thm)],[c_30,c_1975])).

tff(c_1985,plain,(
    ! [A_484] :
      ( k3_relat_1(u1_orders_2(A_484)) = u1_struct_0(A_484)
      | ~ v4_relat_2(u1_orders_2(A_484))
      | ~ v1_relat_2(u1_orders_2(A_484))
      | ~ l1_orders_2(A_484)
      | ~ v4_orders_2(A_484)
      | ~ v2_orders_2(A_484) ) ),
    inference(resolution,[status(thm)],[c_38,c_1980])).

tff(c_1990,plain,(
    ! [A_485] :
      ( k3_relat_1(u1_orders_2(A_485)) = u1_struct_0(A_485)
      | ~ v1_relat_2(u1_orders_2(A_485))
      | ~ v4_orders_2(A_485)
      | ~ l1_orders_2(A_485)
      | ~ v5_orders_2(A_485)
      | ~ v2_orders_2(A_485) ) ),
    inference(resolution,[status(thm)],[c_36,c_1985])).

tff(c_1994,plain,(
    ! [A_33] :
      ( k3_relat_1(u1_orders_2(A_33)) = u1_struct_0(A_33)
      | ~ v4_orders_2(A_33)
      | ~ v5_orders_2(A_33)
      | ~ v2_orders_2(A_33)
      | ~ l1_orders_2(A_33)
      | ~ v3_orders_2(A_33) ) ),
    inference(resolution,[status(thm)],[c_34,c_1990])).

tff(c_1769,plain,(
    ! [A_437] :
      ( m1_subset_1(u1_orders_2(A_437),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_437),u1_struct_0(A_437))))
      | ~ l1_orders_2(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1773,plain,(
    ! [A_437] :
      ( v1_relat_1(u1_orders_2(A_437))
      | ~ l1_orders_2(A_437) ) ),
    inference(resolution,[status(thm)],[c_1769,c_4])).

tff(c_1747,plain,(
    r6_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1996,plain,(
    ! [A_486] :
      ( k3_relat_1(u1_orders_2(A_486)) = u1_struct_0(A_486)
      | ~ v4_orders_2(A_486)
      | ~ v5_orders_2(A_486)
      | ~ v2_orders_2(A_486)
      | ~ l1_orders_2(A_486)
      | ~ v3_orders_2(A_486) ) ),
    inference(resolution,[status(thm)],[c_34,c_1990])).

tff(c_14,plain,(
    ! [B_18,A_12] :
      ( r2_hidden(B_18,k3_relat_1(A_12))
      | ~ r6_orders_1(A_12,B_18)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2061,plain,(
    ! [B_497,A_498] :
      ( r2_hidden(B_497,u1_struct_0(A_498))
      | ~ r6_orders_1(u1_orders_2(A_498),B_497)
      | ~ v1_relat_1(u1_orders_2(A_498))
      | ~ v4_orders_2(A_498)
      | ~ v5_orders_2(A_498)
      | ~ v2_orders_2(A_498)
      | ~ l1_orders_2(A_498)
      | ~ v3_orders_2(A_498) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1996,c_14])).

tff(c_2068,plain,
    ( r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_1747,c_2061])).

tff(c_2072,plain,
    ( r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_77,c_50,c_52,c_2068])).

tff(c_2073,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2072])).

tff(c_2076,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_1773,c_2073])).

tff(c_2080,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2076])).

tff(c_2082,plain,(
    v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2072])).

tff(c_2015,plain,(
    ! [A_486,B_18] :
      ( '#skF_1'(u1_orders_2(A_486),B_18) != B_18
      | r6_orders_1(u1_orders_2(A_486),B_18)
      | ~ r2_hidden(B_18,u1_struct_0(A_486))
      | ~ v1_relat_1(u1_orders_2(A_486))
      | ~ v4_orders_2(A_486)
      | ~ v5_orders_2(A_486)
      | ~ v2_orders_2(A_486)
      | ~ l1_orders_2(A_486)
      | ~ v3_orders_2(A_486) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1996,c_18])).

tff(c_1930,plain,(
    ! [B_470,C_471,A_472] :
      ( r2_hidden(k4_tarski(B_470,C_471),u1_orders_2(A_472))
      | ~ r1_orders_2(A_472,B_470,C_471)
      | ~ m1_subset_1(C_471,u1_struct_0(A_472))
      | ~ m1_subset_1(B_470,u1_struct_0(A_472))
      | ~ l1_orders_2(A_472) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [B_18,C_21,A_12] :
      ( ~ r2_hidden(k4_tarski(B_18,C_21),A_12)
      | C_21 = B_18
      | ~ r2_hidden(C_21,k3_relat_1(A_12))
      | ~ r6_orders_1(A_12,B_18)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2120,plain,(
    ! [C_508,B_509,A_510] :
      ( C_508 = B_509
      | ~ r2_hidden(C_508,k3_relat_1(u1_orders_2(A_510)))
      | ~ r6_orders_1(u1_orders_2(A_510),B_509)
      | ~ v1_relat_1(u1_orders_2(A_510))
      | ~ r1_orders_2(A_510,B_509,C_508)
      | ~ m1_subset_1(C_508,u1_struct_0(A_510))
      | ~ m1_subset_1(B_509,u1_struct_0(A_510))
      | ~ l1_orders_2(A_510) ) ),
    inference(resolution,[status(thm)],[c_1930,c_12])).

tff(c_2148,plain,(
    ! [B_514,B_513,A_515] :
      ( B_514 = B_513
      | ~ r6_orders_1(u1_orders_2(A_515),B_513)
      | ~ r1_orders_2(A_515,B_513,B_514)
      | ~ m1_subset_1(B_514,u1_struct_0(A_515))
      | ~ m1_subset_1(B_513,u1_struct_0(A_515))
      | ~ l1_orders_2(A_515)
      | ~ r6_orders_1(u1_orders_2(A_515),B_514)
      | ~ v1_relat_1(u1_orders_2(A_515)) ) ),
    inference(resolution,[status(thm)],[c_14,c_2120])).

tff(c_2155,plain,(
    ! [B_514] :
      ( B_514 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',B_514)
      | ~ m1_subset_1(B_514,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ r6_orders_1(u1_orders_2('#skF_2'),B_514)
      | ~ v1_relat_1(u1_orders_2('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1747,c_2148])).

tff(c_2161,plain,(
    ! [B_516] :
      ( B_516 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',B_516)
      | ~ m1_subset_1(B_516,u1_struct_0('#skF_2'))
      | ~ r6_orders_1(u1_orders_2('#skF_2'),B_516) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2082,c_48,c_46,c_2155])).

tff(c_2165,plain,(
    ! [B_18] :
      ( B_18 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',B_18)
      | ~ m1_subset_1(B_18,u1_struct_0('#skF_2'))
      | '#skF_1'(u1_orders_2('#skF_2'),B_18) != B_18
      | ~ r2_hidden(B_18,u1_struct_0('#skF_2'))
      | ~ v1_relat_1(u1_orders_2('#skF_2'))
      | ~ v4_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v2_orders_2('#skF_2')
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2015,c_2161])).

tff(c_2183,plain,(
    ! [B_517] :
      ( B_517 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',B_517)
      | ~ m1_subset_1(B_517,u1_struct_0('#skF_2'))
      | '#skF_1'(u1_orders_2('#skF_2'),B_517) != B_517
      | ~ r2_hidden(B_517,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_77,c_50,c_52,c_2082,c_2165])).

tff(c_2200,plain,(
    ! [A_40] :
      ( A_40 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_40)
      | '#skF_1'(u1_orders_2('#skF_2'),A_40) != A_40
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_40,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_44,c_2183])).

tff(c_2201,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2200])).

tff(c_2204,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2201,c_32])).

tff(c_2207,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2204])).

tff(c_2210,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_2207])).

tff(c_2214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2210])).

tff(c_2216,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2200])).

tff(c_2368,plain,(
    ! [B_539,A_540,A_541] :
      ( B_539 = A_540
      | ~ r6_orders_1(u1_orders_2(A_541),B_539)
      | ~ v1_relat_1(u1_orders_2(A_541))
      | ~ r1_orders_2(A_541,B_539,A_540)
      | ~ m1_subset_1(A_540,u1_struct_0(A_541))
      | ~ m1_subset_1(B_539,u1_struct_0(A_541))
      | ~ l1_orders_2(A_541)
      | v1_xboole_0(k3_relat_1(u1_orders_2(A_541)))
      | ~ m1_subset_1(A_540,k3_relat_1(u1_orders_2(A_541))) ) ),
    inference(resolution,[status(thm)],[c_44,c_2120])).

tff(c_2380,plain,(
    ! [A_540] :
      ( A_540 = '#skF_3'
      | ~ v1_relat_1(u1_orders_2('#skF_2'))
      | ~ r1_orders_2('#skF_2','#skF_3',A_540)
      | ~ m1_subset_1(A_540,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | v1_xboole_0(k3_relat_1(u1_orders_2('#skF_2')))
      | ~ m1_subset_1(A_540,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_1747,c_2368])).

tff(c_2387,plain,(
    ! [A_540] :
      ( A_540 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_540)
      | ~ m1_subset_1(A_540,u1_struct_0('#skF_2'))
      | v1_xboole_0(k3_relat_1(u1_orders_2('#skF_2')))
      | ~ m1_subset_1(A_540,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_2082,c_2380])).

tff(c_2388,plain,(
    v1_xboole_0(k3_relat_1(u1_orders_2('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2387])).

tff(c_2391,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1994,c_2388])).

tff(c_2393,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_77,c_50,c_52,c_2391])).

tff(c_2395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2216,c_2393])).

tff(c_2460,plain,(
    ! [A_544] :
      ( A_544 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_544)
      | ~ m1_subset_1(A_544,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_544,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_2387])).

tff(c_2463,plain,(
    ! [A_544] :
      ( A_544 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_544)
      | ~ m1_subset_1(A_544,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_544,u1_struct_0('#skF_2'))
      | ~ v4_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v2_orders_2('#skF_2')
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1994,c_2460])).

tff(c_2485,plain,(
    ! [A_545] :
      ( A_545 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_545)
      | ~ m1_subset_1(A_545,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_77,c_50,c_52,c_2463])).

tff(c_2496,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1741,c_2485])).

tff(c_2506,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1856,c_2496])).

tff(c_2515,plain,(
    r2_orders_2('#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2506,c_1746])).

tff(c_8,plain,(
    ! [A_5,C_11] :
      ( ~ r2_orders_2(A_5,C_11,C_11)
      | ~ m1_subset_1(C_11,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2531,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_2515,c_8])).

tff(c_2538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1741,c_2531])).

%------------------------------------------------------------------------------
