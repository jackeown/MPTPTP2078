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
% DateTime   : Thu Dec  3 10:19:19 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 275 expanded)
%              Number of leaves         :   39 ( 114 expanded)
%              Depth                    :   15
%              Number of atoms          :  276 ( 937 expanded)
%              Number of equality atoms :   26 (  97 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r4_relat_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_relat_2,type,(
    r4_relat_2: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( ( r1_orders_2(A,B,C)
                    & r1_orders_2(A,C,B) )
                 => B = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v5_orders_2(A)
      <=> r4_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_orders_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r4_relat_2(A,B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & r2_hidden(k4_tarski(C,D),A)
                & r2_hidden(k4_tarski(D,C),A) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_2)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_56,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_50,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_999,plain,(
    ! [B_447,C_448,A_449] :
      ( r2_hidden(k4_tarski(B_447,C_448),u1_orders_2(A_449))
      | ~ r1_orders_2(A_449,B_447,C_448)
      | ~ m1_subset_1(C_448,u1_struct_0(A_449))
      | ~ m1_subset_1(B_447,u1_struct_0(A_449))
      | ~ l1_orders_2(A_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1005,plain,(
    ! [A_451,B_452,C_453] :
      ( ~ v1_xboole_0(u1_orders_2(A_451))
      | ~ r1_orders_2(A_451,B_452,C_453)
      | ~ m1_subset_1(C_453,u1_struct_0(A_451))
      | ~ m1_subset_1(B_452,u1_struct_0(A_451))
      | ~ l1_orders_2(A_451) ) ),
    inference(resolution,[status(thm)],[c_999,c_2])).

tff(c_1007,plain,
    ( ~ v1_xboole_0(u1_orders_2('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1005])).

tff(c_1012,plain,(
    ~ v1_xboole_0(u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1007])).

tff(c_22,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_541,plain,(
    ! [A_265] :
      ( m1_subset_1(u1_orders_2(A_265),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_265),u1_struct_0(A_265))))
      | ~ l1_orders_2(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_20,plain,(
    ! [B_17,A_15] :
      ( v1_relat_1(B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_15))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_544,plain,(
    ! [A_265] :
      ( v1_relat_1(u1_orders_2(A_265))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_265),u1_struct_0(A_265)))
      | ~ l1_orders_2(A_265) ) ),
    inference(resolution,[status(thm)],[c_541,c_20])).

tff(c_550,plain,(
    ! [A_265] :
      ( v1_relat_1(u1_orders_2(A_265))
      | ~ l1_orders_2(A_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_544])).

tff(c_46,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_58,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_48,plain,(
    r1_orders_2('#skF_4','#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_38,plain,(
    ! [A_37] :
      ( r4_relat_2(u1_orders_2(A_37),u1_struct_0(A_37))
      | ~ v5_orders_2(A_37)
      | ~ l1_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( v1_xboole_0(k2_zfmisc_1(A_9,B_10))
      | ~ v1_xboole_0(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_63,plain,(
    ! [A_56,B_57] :
      ( v1_xboole_0(k2_zfmisc_1(A_56,B_57))
      | ~ v1_xboole_0(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    ! [A_59,B_60] :
      ( k2_zfmisc_1(A_59,B_60) = k1_xboole_0
      | ~ v1_xboole_0(B_60) ) ),
    inference(resolution,[status(thm)],[c_63,c_6])).

tff(c_100,plain,(
    ! [A_74,A_75,B_76] :
      ( k2_zfmisc_1(A_74,k2_zfmisc_1(A_75,B_76)) = k1_xboole_0
      | ~ v1_xboole_0(B_76) ) ),
    inference(resolution,[status(thm)],[c_12,c_73])).

tff(c_109,plain,(
    ! [A_75,B_76] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k2_zfmisc_1(A_75,B_76))
      | ~ v1_xboole_0(B_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_12])).

tff(c_511,plain,(
    ! [A_250,B_251] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_250,B_251))
      | ~ v1_xboole_0(B_251) ) ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_518,plain,(
    ! [B_10] : ~ v1_xboole_0(B_10) ),
    inference(resolution,[status(thm)],[c_12,c_511])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_519,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_518,c_14])).

tff(c_42,plain,(
    ! [B_42,C_44,A_38] :
      ( r2_hidden(k4_tarski(B_42,C_44),u1_orders_2(A_38))
      | ~ r1_orders_2(A_38,B_42,C_44)
      | ~ m1_subset_1(C_44,u1_struct_0(A_38))
      | ~ m1_subset_1(B_42,u1_struct_0(A_38))
      | ~ l1_orders_2(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_589,plain,(
    ! [D_284,C_285,A_286,B_287] :
      ( D_284 = C_285
      | ~ r2_hidden(k4_tarski(D_284,C_285),A_286)
      | ~ r2_hidden(k4_tarski(C_285,D_284),A_286)
      | ~ r2_hidden(D_284,B_287)
      | ~ r2_hidden(C_285,B_287)
      | ~ r4_relat_2(A_286,B_287)
      | ~ v1_relat_1(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_812,plain,(
    ! [C_406,B_407,A_408,B_409] :
      ( C_406 = B_407
      | ~ r2_hidden(k4_tarski(C_406,B_407),u1_orders_2(A_408))
      | ~ r2_hidden(B_407,B_409)
      | ~ r2_hidden(C_406,B_409)
      | ~ r4_relat_2(u1_orders_2(A_408),B_409)
      | ~ v1_relat_1(u1_orders_2(A_408))
      | ~ r1_orders_2(A_408,B_407,C_406)
      | ~ m1_subset_1(C_406,u1_struct_0(A_408))
      | ~ m1_subset_1(B_407,u1_struct_0(A_408))
      | ~ l1_orders_2(A_408) ) ),
    inference(resolution,[status(thm)],[c_42,c_589])).

tff(c_828,plain,(
    ! [C_410,B_411,B_412,A_413] :
      ( C_410 = B_411
      | ~ r2_hidden(C_410,B_412)
      | ~ r2_hidden(B_411,B_412)
      | ~ r4_relat_2(u1_orders_2(A_413),B_412)
      | ~ v1_relat_1(u1_orders_2(A_413))
      | ~ r1_orders_2(A_413,C_410,B_411)
      | ~ r1_orders_2(A_413,B_411,C_410)
      | ~ m1_subset_1(C_410,u1_struct_0(A_413))
      | ~ m1_subset_1(B_411,u1_struct_0(A_413))
      | ~ l1_orders_2(A_413) ) ),
    inference(resolution,[status(thm)],[c_42,c_812])).

tff(c_850,plain,(
    ! [B_414,A_415,B_416,A_417] :
      ( B_414 = A_415
      | ~ r2_hidden(B_414,B_416)
      | ~ r4_relat_2(u1_orders_2(A_417),B_416)
      | ~ v1_relat_1(u1_orders_2(A_417))
      | ~ r1_orders_2(A_417,A_415,B_414)
      | ~ r1_orders_2(A_417,B_414,A_415)
      | ~ m1_subset_1(A_415,u1_struct_0(A_417))
      | ~ m1_subset_1(B_414,u1_struct_0(A_417))
      | ~ l1_orders_2(A_417)
      | ~ m1_subset_1(A_415,B_416) ) ),
    inference(resolution,[status(thm)],[c_519,c_828])).

tff(c_872,plain,(
    ! [A_419,A_418,A_420,B_421] :
      ( A_419 = A_418
      | ~ r4_relat_2(u1_orders_2(A_420),B_421)
      | ~ v1_relat_1(u1_orders_2(A_420))
      | ~ r1_orders_2(A_420,A_418,A_419)
      | ~ r1_orders_2(A_420,A_419,A_418)
      | ~ m1_subset_1(A_418,u1_struct_0(A_420))
      | ~ m1_subset_1(A_419,u1_struct_0(A_420))
      | ~ l1_orders_2(A_420)
      | ~ m1_subset_1(A_418,B_421)
      | ~ m1_subset_1(A_419,B_421) ) ),
    inference(resolution,[status(thm)],[c_519,c_850])).

tff(c_880,plain,(
    ! [A_423,A_422,A_424] :
      ( A_423 = A_422
      | ~ v1_relat_1(u1_orders_2(A_424))
      | ~ r1_orders_2(A_424,A_423,A_422)
      | ~ r1_orders_2(A_424,A_422,A_423)
      | ~ m1_subset_1(A_423,u1_struct_0(A_424))
      | ~ m1_subset_1(A_422,u1_struct_0(A_424))
      | ~ v5_orders_2(A_424)
      | ~ l1_orders_2(A_424) ) ),
    inference(resolution,[status(thm)],[c_38,c_872])).

tff(c_886,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_4'))
    | ~ r1_orders_2('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ v5_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_880])).

tff(c_893,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_52,c_54,c_48,c_886])).

tff(c_894,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_893])).

tff(c_901,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_550,c_894])).

tff(c_905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_901])).

tff(c_906,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_67,plain,(
    ! [A_56,B_57] :
      ( k2_zfmisc_1(A_56,B_57) = k1_xboole_0
      | ~ v1_xboole_0(B_57) ) ),
    inference(resolution,[status(thm)],[c_63,c_6])).

tff(c_912,plain,(
    ! [A_56] : k2_zfmisc_1(A_56,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_906,c_67])).

tff(c_964,plain,(
    ! [A_437] :
      ( m1_subset_1(u1_orders_2(A_437),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_437),u1_struct_0(A_437))))
      | ~ l1_orders_2(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_967,plain,(
    ! [A_437] :
      ( v1_relat_1(u1_orders_2(A_437))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_437),u1_struct_0(A_437)))
      | ~ l1_orders_2(A_437) ) ),
    inference(resolution,[status(thm)],[c_964,c_20])).

tff(c_973,plain,(
    ! [A_437] :
      ( v1_relat_1(u1_orders_2(A_437))
      | ~ l1_orders_2(A_437) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_967])).

tff(c_1035,plain,(
    ! [D_457,C_458,A_459,B_460] :
      ( D_457 = C_458
      | ~ r2_hidden(k4_tarski(D_457,C_458),A_459)
      | ~ r2_hidden(k4_tarski(C_458,D_457),A_459)
      | ~ r2_hidden(D_457,B_460)
      | ~ r2_hidden(C_458,B_460)
      | ~ r4_relat_2(A_459,B_460)
      | ~ v1_relat_1(A_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1226,plain,(
    ! [C_535,B_536,A_537,B_538] :
      ( C_535 = B_536
      | ~ r2_hidden(k4_tarski(C_535,B_536),u1_orders_2(A_537))
      | ~ r2_hidden(B_536,B_538)
      | ~ r2_hidden(C_535,B_538)
      | ~ r4_relat_2(u1_orders_2(A_537),B_538)
      | ~ v1_relat_1(u1_orders_2(A_537))
      | ~ r1_orders_2(A_537,B_536,C_535)
      | ~ m1_subset_1(C_535,u1_struct_0(A_537))
      | ~ m1_subset_1(B_536,u1_struct_0(A_537))
      | ~ l1_orders_2(A_537) ) ),
    inference(resolution,[status(thm)],[c_42,c_1035])).

tff(c_1242,plain,(
    ! [C_539,B_540,B_541,A_542] :
      ( C_539 = B_540
      | ~ r2_hidden(C_539,B_541)
      | ~ r2_hidden(B_540,B_541)
      | ~ r4_relat_2(u1_orders_2(A_542),B_541)
      | ~ v1_relat_1(u1_orders_2(A_542))
      | ~ r1_orders_2(A_542,C_539,B_540)
      | ~ r1_orders_2(A_542,B_540,C_539)
      | ~ m1_subset_1(C_539,u1_struct_0(A_542))
      | ~ m1_subset_1(B_540,u1_struct_0(A_542))
      | ~ l1_orders_2(A_542) ) ),
    inference(resolution,[status(thm)],[c_42,c_1226])).

tff(c_1286,plain,(
    ! [B_547,A_548,B_549,A_550] :
      ( B_547 = A_548
      | ~ r2_hidden(B_547,B_549)
      | ~ r4_relat_2(u1_orders_2(A_550),B_549)
      | ~ v1_relat_1(u1_orders_2(A_550))
      | ~ r1_orders_2(A_550,A_548,B_547)
      | ~ r1_orders_2(A_550,B_547,A_548)
      | ~ m1_subset_1(A_548,u1_struct_0(A_550))
      | ~ m1_subset_1(B_547,u1_struct_0(A_550))
      | ~ l1_orders_2(A_550)
      | v1_xboole_0(B_549)
      | ~ m1_subset_1(A_548,B_549) ) ),
    inference(resolution,[status(thm)],[c_14,c_1242])).

tff(c_1318,plain,(
    ! [A_560,A_559,A_561,B_562] :
      ( A_560 = A_559
      | ~ r4_relat_2(u1_orders_2(A_561),B_562)
      | ~ v1_relat_1(u1_orders_2(A_561))
      | ~ r1_orders_2(A_561,A_559,A_560)
      | ~ r1_orders_2(A_561,A_560,A_559)
      | ~ m1_subset_1(A_559,u1_struct_0(A_561))
      | ~ m1_subset_1(A_560,u1_struct_0(A_561))
      | ~ l1_orders_2(A_561)
      | ~ m1_subset_1(A_559,B_562)
      | v1_xboole_0(B_562)
      | ~ m1_subset_1(A_560,B_562) ) ),
    inference(resolution,[status(thm)],[c_14,c_1286])).

tff(c_1334,plain,(
    ! [A_564,A_563,A_565] :
      ( A_564 = A_563
      | ~ v1_relat_1(u1_orders_2(A_565))
      | ~ r1_orders_2(A_565,A_564,A_563)
      | ~ r1_orders_2(A_565,A_563,A_564)
      | ~ m1_subset_1(A_564,u1_struct_0(A_565))
      | v1_xboole_0(u1_struct_0(A_565))
      | ~ m1_subset_1(A_563,u1_struct_0(A_565))
      | ~ v5_orders_2(A_565)
      | ~ l1_orders_2(A_565) ) ),
    inference(resolution,[status(thm)],[c_38,c_1318])).

tff(c_1340,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_4'))
    | ~ r1_orders_2('#skF_4','#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ v5_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1334])).

tff(c_1347,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_52,c_54,c_48,c_1340])).

tff(c_1348,plain,
    ( ~ v1_relat_1(u1_orders_2('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1347])).

tff(c_1353,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1348])).

tff(c_1356,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_973,c_1353])).

tff(c_1360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1356])).

tff(c_1361,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1348])).

tff(c_1375,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1361,c_6])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_974,plain,(
    ! [A_437] :
      ( r1_tarski(u1_orders_2(A_437),k2_zfmisc_1(u1_struct_0(A_437),u1_struct_0(A_437)))
      | ~ l1_orders_2(A_437) ) ),
    inference(resolution,[status(thm)],[c_964,c_16])).

tff(c_1386,plain,
    ( r1_tarski(u1_orders_2('#skF_4'),k2_zfmisc_1(k1_xboole_0,u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1375,c_974])).

tff(c_1410,plain,(
    r1_tarski(u1_orders_2('#skF_4'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_912,c_1375,c_1386])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83,plain,(
    ! [B_65,A_66] :
      ( ~ r1_xboole_0(B_65,A_66)
      | ~ r1_tarski(B_65,A_66)
      | v1_xboole_0(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_87,plain,(
    ! [A_6] :
      ( ~ r1_tarski(A_6,k1_xboole_0)
      | v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_83])).

tff(c_1431,plain,(
    v1_xboole_0(u1_orders_2('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1410,c_87])).

tff(c_1438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1012,c_1431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.81  
% 4.62/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.75/1.81  %$ r1_orders_2 > r4_relat_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 4.75/1.81  
% 4.75/1.81  %Foreground sorts:
% 4.75/1.81  
% 4.75/1.81  
% 4.75/1.81  %Background operators:
% 4.75/1.81  
% 4.75/1.81  
% 4.75/1.81  %Foreground operators:
% 4.75/1.81  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 4.75/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.75/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.75/1.81  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.75/1.81  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.75/1.81  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.75/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.75/1.81  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.75/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.75/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.75/1.81  tff('#skF_6', type, '#skF_6': $i).
% 4.75/1.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.75/1.81  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.75/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.75/1.81  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.75/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.75/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.75/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.75/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.75/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.75/1.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.75/1.81  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 4.75/1.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.75/1.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.75/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.75/1.81  
% 4.83/1.83  tff(f_123, negated_conjecture, ~(![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_orders_2)).
% 4.83/1.83  tff(f_102, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 4.83/1.83  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.83/1.83  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.83/1.83  tff(f_106, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 4.83/1.83  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.83/1.83  tff(f_90, axiom, (![A]: (l1_orders_2(A) => (v5_orders_2(A) <=> r4_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_orders_2)).
% 4.83/1.83  tff(f_49, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 4.83/1.83  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.83/1.83  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.83/1.83  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (![B]: (r4_relat_2(A, B) <=> (![C, D]: ((((r2_hidden(C, B) & r2_hidden(D, B)) & r2_hidden(k4_tarski(C, D), A)) & r2_hidden(k4_tarski(D, C), A)) => (C = D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_2)).
% 4.83/1.83  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.83/1.83  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.83/1.83  tff(f_45, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.83/1.83  tff(c_56, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.83/1.83  tff(c_54, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.83/1.83  tff(c_52, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.83/1.83  tff(c_50, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.83/1.83  tff(c_999, plain, (![B_447, C_448, A_449]: (r2_hidden(k4_tarski(B_447, C_448), u1_orders_2(A_449)) | ~r1_orders_2(A_449, B_447, C_448) | ~m1_subset_1(C_448, u1_struct_0(A_449)) | ~m1_subset_1(B_447, u1_struct_0(A_449)) | ~l1_orders_2(A_449))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.83/1.83  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.83/1.83  tff(c_1005, plain, (![A_451, B_452, C_453]: (~v1_xboole_0(u1_orders_2(A_451)) | ~r1_orders_2(A_451, B_452, C_453) | ~m1_subset_1(C_453, u1_struct_0(A_451)) | ~m1_subset_1(B_452, u1_struct_0(A_451)) | ~l1_orders_2(A_451))), inference(resolution, [status(thm)], [c_999, c_2])).
% 4.83/1.83  tff(c_1007, plain, (~v1_xboole_0(u1_orders_2('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1005])).
% 4.83/1.83  tff(c_1012, plain, (~v1_xboole_0(u1_orders_2('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_1007])).
% 4.83/1.83  tff(c_22, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.83/1.83  tff(c_541, plain, (![A_265]: (m1_subset_1(u1_orders_2(A_265), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_265), u1_struct_0(A_265)))) | ~l1_orders_2(A_265))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.83/1.83  tff(c_20, plain, (![B_17, A_15]: (v1_relat_1(B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_15)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.83/1.83  tff(c_544, plain, (![A_265]: (v1_relat_1(u1_orders_2(A_265)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_265), u1_struct_0(A_265))) | ~l1_orders_2(A_265))), inference(resolution, [status(thm)], [c_541, c_20])).
% 4.83/1.83  tff(c_550, plain, (![A_265]: (v1_relat_1(u1_orders_2(A_265)) | ~l1_orders_2(A_265))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_544])).
% 4.83/1.83  tff(c_46, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.83/1.83  tff(c_58, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.83/1.83  tff(c_48, plain, (r1_orders_2('#skF_4', '#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.83/1.83  tff(c_38, plain, (![A_37]: (r4_relat_2(u1_orders_2(A_37), u1_struct_0(A_37)) | ~v5_orders_2(A_37) | ~l1_orders_2(A_37))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.83/1.83  tff(c_12, plain, (![A_9, B_10]: (v1_xboole_0(k2_zfmisc_1(A_9, B_10)) | ~v1_xboole_0(B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.83/1.83  tff(c_63, plain, (![A_56, B_57]: (v1_xboole_0(k2_zfmisc_1(A_56, B_57)) | ~v1_xboole_0(B_57))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.83/1.83  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.83/1.83  tff(c_73, plain, (![A_59, B_60]: (k2_zfmisc_1(A_59, B_60)=k1_xboole_0 | ~v1_xboole_0(B_60))), inference(resolution, [status(thm)], [c_63, c_6])).
% 4.83/1.83  tff(c_100, plain, (![A_74, A_75, B_76]: (k2_zfmisc_1(A_74, k2_zfmisc_1(A_75, B_76))=k1_xboole_0 | ~v1_xboole_0(B_76))), inference(resolution, [status(thm)], [c_12, c_73])).
% 4.83/1.83  tff(c_109, plain, (![A_75, B_76]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k2_zfmisc_1(A_75, B_76)) | ~v1_xboole_0(B_76))), inference(superposition, [status(thm), theory('equality')], [c_100, c_12])).
% 4.83/1.83  tff(c_511, plain, (![A_250, B_251]: (~v1_xboole_0(k2_zfmisc_1(A_250, B_251)) | ~v1_xboole_0(B_251))), inference(splitLeft, [status(thm)], [c_109])).
% 4.83/1.83  tff(c_518, plain, (![B_10]: (~v1_xboole_0(B_10))), inference(resolution, [status(thm)], [c_12, c_511])).
% 4.83/1.83  tff(c_14, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.83/1.83  tff(c_519, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | ~m1_subset_1(A_11, B_12))), inference(negUnitSimplification, [status(thm)], [c_518, c_14])).
% 4.83/1.83  tff(c_42, plain, (![B_42, C_44, A_38]: (r2_hidden(k4_tarski(B_42, C_44), u1_orders_2(A_38)) | ~r1_orders_2(A_38, B_42, C_44) | ~m1_subset_1(C_44, u1_struct_0(A_38)) | ~m1_subset_1(B_42, u1_struct_0(A_38)) | ~l1_orders_2(A_38))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.83/1.83  tff(c_589, plain, (![D_284, C_285, A_286, B_287]: (D_284=C_285 | ~r2_hidden(k4_tarski(D_284, C_285), A_286) | ~r2_hidden(k4_tarski(C_285, D_284), A_286) | ~r2_hidden(D_284, B_287) | ~r2_hidden(C_285, B_287) | ~r4_relat_2(A_286, B_287) | ~v1_relat_1(A_286))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.83/1.83  tff(c_812, plain, (![C_406, B_407, A_408, B_409]: (C_406=B_407 | ~r2_hidden(k4_tarski(C_406, B_407), u1_orders_2(A_408)) | ~r2_hidden(B_407, B_409) | ~r2_hidden(C_406, B_409) | ~r4_relat_2(u1_orders_2(A_408), B_409) | ~v1_relat_1(u1_orders_2(A_408)) | ~r1_orders_2(A_408, B_407, C_406) | ~m1_subset_1(C_406, u1_struct_0(A_408)) | ~m1_subset_1(B_407, u1_struct_0(A_408)) | ~l1_orders_2(A_408))), inference(resolution, [status(thm)], [c_42, c_589])).
% 4.83/1.83  tff(c_828, plain, (![C_410, B_411, B_412, A_413]: (C_410=B_411 | ~r2_hidden(C_410, B_412) | ~r2_hidden(B_411, B_412) | ~r4_relat_2(u1_orders_2(A_413), B_412) | ~v1_relat_1(u1_orders_2(A_413)) | ~r1_orders_2(A_413, C_410, B_411) | ~r1_orders_2(A_413, B_411, C_410) | ~m1_subset_1(C_410, u1_struct_0(A_413)) | ~m1_subset_1(B_411, u1_struct_0(A_413)) | ~l1_orders_2(A_413))), inference(resolution, [status(thm)], [c_42, c_812])).
% 4.83/1.83  tff(c_850, plain, (![B_414, A_415, B_416, A_417]: (B_414=A_415 | ~r2_hidden(B_414, B_416) | ~r4_relat_2(u1_orders_2(A_417), B_416) | ~v1_relat_1(u1_orders_2(A_417)) | ~r1_orders_2(A_417, A_415, B_414) | ~r1_orders_2(A_417, B_414, A_415) | ~m1_subset_1(A_415, u1_struct_0(A_417)) | ~m1_subset_1(B_414, u1_struct_0(A_417)) | ~l1_orders_2(A_417) | ~m1_subset_1(A_415, B_416))), inference(resolution, [status(thm)], [c_519, c_828])).
% 4.83/1.83  tff(c_872, plain, (![A_419, A_418, A_420, B_421]: (A_419=A_418 | ~r4_relat_2(u1_orders_2(A_420), B_421) | ~v1_relat_1(u1_orders_2(A_420)) | ~r1_orders_2(A_420, A_418, A_419) | ~r1_orders_2(A_420, A_419, A_418) | ~m1_subset_1(A_418, u1_struct_0(A_420)) | ~m1_subset_1(A_419, u1_struct_0(A_420)) | ~l1_orders_2(A_420) | ~m1_subset_1(A_418, B_421) | ~m1_subset_1(A_419, B_421))), inference(resolution, [status(thm)], [c_519, c_850])).
% 4.83/1.83  tff(c_880, plain, (![A_423, A_422, A_424]: (A_423=A_422 | ~v1_relat_1(u1_orders_2(A_424)) | ~r1_orders_2(A_424, A_423, A_422) | ~r1_orders_2(A_424, A_422, A_423) | ~m1_subset_1(A_423, u1_struct_0(A_424)) | ~m1_subset_1(A_422, u1_struct_0(A_424)) | ~v5_orders_2(A_424) | ~l1_orders_2(A_424))), inference(resolution, [status(thm)], [c_38, c_872])).
% 4.83/1.83  tff(c_886, plain, ('#skF_5'='#skF_6' | ~v1_relat_1(u1_orders_2('#skF_4')) | ~r1_orders_2('#skF_4', '#skF_6', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~v5_orders_2('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_50, c_880])).
% 4.83/1.83  tff(c_893, plain, ('#skF_5'='#skF_6' | ~v1_relat_1(u1_orders_2('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_52, c_54, c_48, c_886])).
% 4.83/1.83  tff(c_894, plain, (~v1_relat_1(u1_orders_2('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_46, c_893])).
% 4.83/1.83  tff(c_901, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_550, c_894])).
% 4.83/1.83  tff(c_905, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_901])).
% 4.83/1.83  tff(c_906, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_109])).
% 4.83/1.83  tff(c_67, plain, (![A_56, B_57]: (k2_zfmisc_1(A_56, B_57)=k1_xboole_0 | ~v1_xboole_0(B_57))), inference(resolution, [status(thm)], [c_63, c_6])).
% 4.83/1.83  tff(c_912, plain, (![A_56]: (k2_zfmisc_1(A_56, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_906, c_67])).
% 4.83/1.83  tff(c_964, plain, (![A_437]: (m1_subset_1(u1_orders_2(A_437), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_437), u1_struct_0(A_437)))) | ~l1_orders_2(A_437))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.83/1.83  tff(c_967, plain, (![A_437]: (v1_relat_1(u1_orders_2(A_437)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_437), u1_struct_0(A_437))) | ~l1_orders_2(A_437))), inference(resolution, [status(thm)], [c_964, c_20])).
% 4.83/1.83  tff(c_973, plain, (![A_437]: (v1_relat_1(u1_orders_2(A_437)) | ~l1_orders_2(A_437))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_967])).
% 4.83/1.83  tff(c_1035, plain, (![D_457, C_458, A_459, B_460]: (D_457=C_458 | ~r2_hidden(k4_tarski(D_457, C_458), A_459) | ~r2_hidden(k4_tarski(C_458, D_457), A_459) | ~r2_hidden(D_457, B_460) | ~r2_hidden(C_458, B_460) | ~r4_relat_2(A_459, B_460) | ~v1_relat_1(A_459))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.83/1.83  tff(c_1226, plain, (![C_535, B_536, A_537, B_538]: (C_535=B_536 | ~r2_hidden(k4_tarski(C_535, B_536), u1_orders_2(A_537)) | ~r2_hidden(B_536, B_538) | ~r2_hidden(C_535, B_538) | ~r4_relat_2(u1_orders_2(A_537), B_538) | ~v1_relat_1(u1_orders_2(A_537)) | ~r1_orders_2(A_537, B_536, C_535) | ~m1_subset_1(C_535, u1_struct_0(A_537)) | ~m1_subset_1(B_536, u1_struct_0(A_537)) | ~l1_orders_2(A_537))), inference(resolution, [status(thm)], [c_42, c_1035])).
% 4.83/1.83  tff(c_1242, plain, (![C_539, B_540, B_541, A_542]: (C_539=B_540 | ~r2_hidden(C_539, B_541) | ~r2_hidden(B_540, B_541) | ~r4_relat_2(u1_orders_2(A_542), B_541) | ~v1_relat_1(u1_orders_2(A_542)) | ~r1_orders_2(A_542, C_539, B_540) | ~r1_orders_2(A_542, B_540, C_539) | ~m1_subset_1(C_539, u1_struct_0(A_542)) | ~m1_subset_1(B_540, u1_struct_0(A_542)) | ~l1_orders_2(A_542))), inference(resolution, [status(thm)], [c_42, c_1226])).
% 4.83/1.83  tff(c_1286, plain, (![B_547, A_548, B_549, A_550]: (B_547=A_548 | ~r2_hidden(B_547, B_549) | ~r4_relat_2(u1_orders_2(A_550), B_549) | ~v1_relat_1(u1_orders_2(A_550)) | ~r1_orders_2(A_550, A_548, B_547) | ~r1_orders_2(A_550, B_547, A_548) | ~m1_subset_1(A_548, u1_struct_0(A_550)) | ~m1_subset_1(B_547, u1_struct_0(A_550)) | ~l1_orders_2(A_550) | v1_xboole_0(B_549) | ~m1_subset_1(A_548, B_549))), inference(resolution, [status(thm)], [c_14, c_1242])).
% 4.83/1.83  tff(c_1318, plain, (![A_560, A_559, A_561, B_562]: (A_560=A_559 | ~r4_relat_2(u1_orders_2(A_561), B_562) | ~v1_relat_1(u1_orders_2(A_561)) | ~r1_orders_2(A_561, A_559, A_560) | ~r1_orders_2(A_561, A_560, A_559) | ~m1_subset_1(A_559, u1_struct_0(A_561)) | ~m1_subset_1(A_560, u1_struct_0(A_561)) | ~l1_orders_2(A_561) | ~m1_subset_1(A_559, B_562) | v1_xboole_0(B_562) | ~m1_subset_1(A_560, B_562))), inference(resolution, [status(thm)], [c_14, c_1286])).
% 4.83/1.83  tff(c_1334, plain, (![A_564, A_563, A_565]: (A_564=A_563 | ~v1_relat_1(u1_orders_2(A_565)) | ~r1_orders_2(A_565, A_564, A_563) | ~r1_orders_2(A_565, A_563, A_564) | ~m1_subset_1(A_564, u1_struct_0(A_565)) | v1_xboole_0(u1_struct_0(A_565)) | ~m1_subset_1(A_563, u1_struct_0(A_565)) | ~v5_orders_2(A_565) | ~l1_orders_2(A_565))), inference(resolution, [status(thm)], [c_38, c_1318])).
% 4.83/1.83  tff(c_1340, plain, ('#skF_5'='#skF_6' | ~v1_relat_1(u1_orders_2('#skF_4')) | ~r1_orders_2('#skF_4', '#skF_6', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~v5_orders_2('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1334])).
% 4.83/1.83  tff(c_1347, plain, ('#skF_5'='#skF_6' | ~v1_relat_1(u1_orders_2('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_52, c_54, c_48, c_1340])).
% 4.83/1.83  tff(c_1348, plain, (~v1_relat_1(u1_orders_2('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_46, c_1347])).
% 4.83/1.83  tff(c_1353, plain, (~v1_relat_1(u1_orders_2('#skF_4'))), inference(splitLeft, [status(thm)], [c_1348])).
% 4.83/1.83  tff(c_1356, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_973, c_1353])).
% 4.83/1.83  tff(c_1360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_1356])).
% 4.83/1.83  tff(c_1361, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1348])).
% 4.83/1.83  tff(c_1375, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1361, c_6])).
% 4.83/1.83  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.83/1.83  tff(c_974, plain, (![A_437]: (r1_tarski(u1_orders_2(A_437), k2_zfmisc_1(u1_struct_0(A_437), u1_struct_0(A_437))) | ~l1_orders_2(A_437))), inference(resolution, [status(thm)], [c_964, c_16])).
% 4.83/1.83  tff(c_1386, plain, (r1_tarski(u1_orders_2('#skF_4'), k2_zfmisc_1(k1_xboole_0, u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1375, c_974])).
% 4.83/1.83  tff(c_1410, plain, (r1_tarski(u1_orders_2('#skF_4'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_912, c_1375, c_1386])).
% 4.83/1.83  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.83/1.83  tff(c_83, plain, (![B_65, A_66]: (~r1_xboole_0(B_65, A_66) | ~r1_tarski(B_65, A_66) | v1_xboole_0(B_65))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.83/1.83  tff(c_87, plain, (![A_6]: (~r1_tarski(A_6, k1_xboole_0) | v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_8, c_83])).
% 4.83/1.83  tff(c_1431, plain, (v1_xboole_0(u1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_1410, c_87])).
% 4.83/1.83  tff(c_1438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1012, c_1431])).
% 4.83/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.83  
% 4.83/1.83  Inference rules
% 4.83/1.83  ----------------------
% 4.83/1.83  #Ref     : 0
% 4.83/1.83  #Sup     : 312
% 4.83/1.83  #Fact    : 0
% 4.83/1.83  #Define  : 0
% 4.83/1.83  #Split   : 3
% 4.83/1.83  #Chain   : 0
% 4.83/1.83  #Close   : 0
% 4.83/1.83  
% 4.83/1.83  Ordering : KBO
% 4.83/1.83  
% 4.83/1.83  Simplification rules
% 4.83/1.83  ----------------------
% 4.83/1.83  #Subsume      : 51
% 4.83/1.83  #Demod        : 85
% 4.83/1.83  #Tautology    : 38
% 4.83/1.83  #SimpNegUnit  : 18
% 4.83/1.83  #BackRed      : 11
% 4.83/1.83  
% 4.83/1.83  #Partial instantiations: 0
% 4.83/1.83  #Strategies tried      : 1
% 4.83/1.83  
% 4.83/1.83  Timing (in seconds)
% 4.83/1.83  ----------------------
% 4.83/1.83  Preprocessing        : 0.31
% 4.83/1.83  Parsing              : 0.17
% 4.83/1.83  CNF conversion       : 0.02
% 4.83/1.83  Main loop            : 0.73
% 4.83/1.83  Inferencing          : 0.27
% 4.83/1.83  Reduction            : 0.17
% 4.83/1.83  Demodulation         : 0.11
% 4.83/1.83  BG Simplification    : 0.03
% 4.83/1.83  Subsumption          : 0.20
% 4.83/1.83  Abstraction          : 0.03
% 4.83/1.83  MUC search           : 0.00
% 4.83/1.83  Cooper               : 0.00
% 4.83/1.84  Total                : 1.09
% 4.83/1.84  Index Insertion      : 0.00
% 4.83/1.84  Index Deletion       : 0.00
% 4.83/1.84  Index Matching       : 0.00
% 4.83/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
