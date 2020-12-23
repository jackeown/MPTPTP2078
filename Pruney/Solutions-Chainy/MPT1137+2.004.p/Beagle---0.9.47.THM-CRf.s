%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:19 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 447 expanded)
%              Number of leaves         :   37 ( 173 expanded)
%              Depth                    :   18
%              Number of atoms          :  284 (1608 expanded)
%              Number of equality atoms :   27 ( 161 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v1_subset_1 > r4_relat_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_relat_2,type,(
    r4_relat_2: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_126,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v5_orders_2(A)
      <=> r4_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_orders_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_87,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(c_52,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_16,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_787,plain,(
    ! [A_222] :
      ( m1_subset_1(u1_orders_2(A_222),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_222),u1_struct_0(A_222))))
      | ~ l1_orders_2(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_14,plain,(
    ! [B_14,A_12] :
      ( v1_relat_1(B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_12))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_798,plain,(
    ! [A_222] :
      ( v1_relat_1(u1_orders_2(A_222))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_222),u1_struct_0(A_222)))
      | ~ l1_orders_2(A_222) ) ),
    inference(resolution,[status(thm)],[c_787,c_14])).

tff(c_804,plain,(
    ! [A_222] :
      ( v1_relat_1(u1_orders_2(A_222))
      | ~ l1_orders_2(A_222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_798])).

tff(c_42,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_46,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_44,plain,(
    r1_orders_2('#skF_4','#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_34,plain,(
    ! [A_38] :
      ( r4_relat_2(u1_orders_2(A_38),u1_struct_0(A_38))
      | ~ v5_orders_2(A_38)
      | ~ l1_orders_2(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_38,plain,(
    ! [B_43,C_45,A_39] :
      ( r2_hidden(k4_tarski(B_43,C_45),u1_orders_2(A_39))
      | ~ r1_orders_2(A_39,B_43,C_45)
      | ~ m1_subset_1(C_45,u1_struct_0(A_39))
      | ~ m1_subset_1(B_43,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_894,plain,(
    ! [D_244,C_245,A_246,B_247] :
      ( D_244 = C_245
      | ~ r2_hidden(k4_tarski(D_244,C_245),A_246)
      | ~ r2_hidden(k4_tarski(C_245,D_244),A_246)
      | ~ r2_hidden(D_244,B_247)
      | ~ r2_hidden(C_245,B_247)
      | ~ r4_relat_2(A_246,B_247)
      | ~ v1_relat_1(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1021,plain,(
    ! [C_295,B_296,A_297,B_298] :
      ( C_295 = B_296
      | ~ r2_hidden(k4_tarski(C_295,B_296),u1_orders_2(A_297))
      | ~ r2_hidden(B_296,B_298)
      | ~ r2_hidden(C_295,B_298)
      | ~ r4_relat_2(u1_orders_2(A_297),B_298)
      | ~ v1_relat_1(u1_orders_2(A_297))
      | ~ r1_orders_2(A_297,B_296,C_295)
      | ~ m1_subset_1(C_295,u1_struct_0(A_297))
      | ~ m1_subset_1(B_296,u1_struct_0(A_297))
      | ~ l1_orders_2(A_297) ) ),
    inference(resolution,[status(thm)],[c_38,c_894])).

tff(c_1037,plain,(
    ! [C_299,B_300,B_301,A_302] :
      ( C_299 = B_300
      | ~ r2_hidden(C_299,B_301)
      | ~ r2_hidden(B_300,B_301)
      | ~ r4_relat_2(u1_orders_2(A_302),B_301)
      | ~ v1_relat_1(u1_orders_2(A_302))
      | ~ r1_orders_2(A_302,C_299,B_300)
      | ~ r1_orders_2(A_302,B_300,C_299)
      | ~ m1_subset_1(C_299,u1_struct_0(A_302))
      | ~ m1_subset_1(B_300,u1_struct_0(A_302))
      | ~ l1_orders_2(A_302) ) ),
    inference(resolution,[status(thm)],[c_38,c_1021])).

tff(c_1056,plain,(
    ! [B_303,A_304,B_305,A_306] :
      ( B_303 = A_304
      | ~ r2_hidden(B_303,B_305)
      | ~ r4_relat_2(u1_orders_2(A_306),B_305)
      | ~ v1_relat_1(u1_orders_2(A_306))
      | ~ r1_orders_2(A_306,A_304,B_303)
      | ~ r1_orders_2(A_306,B_303,A_304)
      | ~ m1_subset_1(A_304,u1_struct_0(A_306))
      | ~ m1_subset_1(B_303,u1_struct_0(A_306))
      | ~ l1_orders_2(A_306)
      | v1_xboole_0(B_305)
      | ~ m1_subset_1(A_304,B_305) ) ),
    inference(resolution,[status(thm)],[c_10,c_1037])).

tff(c_1096,plain,(
    ! [A_320,A_319,A_321,B_322] :
      ( A_320 = A_319
      | ~ r4_relat_2(u1_orders_2(A_321),B_322)
      | ~ v1_relat_1(u1_orders_2(A_321))
      | ~ r1_orders_2(A_321,A_320,A_319)
      | ~ r1_orders_2(A_321,A_319,A_320)
      | ~ m1_subset_1(A_320,u1_struct_0(A_321))
      | ~ m1_subset_1(A_319,u1_struct_0(A_321))
      | ~ l1_orders_2(A_321)
      | ~ m1_subset_1(A_320,B_322)
      | v1_xboole_0(B_322)
      | ~ m1_subset_1(A_319,B_322) ) ),
    inference(resolution,[status(thm)],[c_10,c_1056])).

tff(c_1113,plain,(
    ! [A_324,A_323,A_325] :
      ( A_324 = A_323
      | ~ v1_relat_1(u1_orders_2(A_325))
      | ~ r1_orders_2(A_325,A_323,A_324)
      | ~ r1_orders_2(A_325,A_324,A_323)
      | ~ m1_subset_1(A_323,u1_struct_0(A_325))
      | v1_xboole_0(u1_struct_0(A_325))
      | ~ m1_subset_1(A_324,u1_struct_0(A_325))
      | ~ v5_orders_2(A_325)
      | ~ l1_orders_2(A_325) ) ),
    inference(resolution,[status(thm)],[c_34,c_1096])).

tff(c_1119,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_4'))
    | ~ r1_orders_2('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v5_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1113])).

tff(c_1126,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_50,c_48,c_46,c_1119])).

tff(c_1127,plain,
    ( ~ v1_relat_1(u1_orders_2('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1126])).

tff(c_1132,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1127])).

tff(c_1135,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_804,c_1132])).

tff(c_1139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1135])).

tff(c_1140,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1127])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1155,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1140,c_2])).

tff(c_1158,plain,(
    m1_subset_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1155,c_48])).

tff(c_1157,plain,(
    m1_subset_1('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1155,c_50])).

tff(c_164,plain,(
    ! [A_83] :
      ( m1_subset_1(u1_orders_2(A_83),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_83),u1_struct_0(A_83))))
      | ~ l1_orders_2(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_167,plain,(
    ! [A_83] :
      ( v1_relat_1(u1_orders_2(A_83))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_83),u1_struct_0(A_83)))
      | ~ l1_orders_2(A_83) ) ),
    inference(resolution,[status(thm)],[c_164,c_14])).

tff(c_170,plain,(
    ! [A_83] :
      ( v1_relat_1(u1_orders_2(A_83))
      | ~ l1_orders_2(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_167])).

tff(c_8,plain,(
    ! [A_5] : m1_subset_1('#skF_1'(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,(
    ! [B_59,A_60] :
      ( v1_xboole_0(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_69,plain,(
    ! [A_5] :
      ( v1_xboole_0('#skF_1'(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_8,c_65])).

tff(c_70,plain,(
    ! [A_61] :
      ( v1_xboole_0('#skF_1'(A_61))
      | ~ v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_8,c_65])).

tff(c_76,plain,(
    ! [A_64] :
      ( '#skF_1'(A_64) = k1_xboole_0
      | ~ v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_81,plain,(
    ! [A_65] :
      ( '#skF_1'('#skF_1'(A_65)) = k1_xboole_0
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_69,c_76])).

tff(c_90,plain,(
    ! [A_65] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0('#skF_1'(A_65))
      | ~ v1_xboole_0(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_69])).

tff(c_141,plain,(
    ! [A_73] :
      ( ~ v1_xboole_0('#skF_1'(A_73))
      | ~ v1_xboole_0(A_73) ) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_148,plain,(
    ! [A_5] : ~ v1_xboole_0(A_5) ),
    inference(resolution,[status(thm)],[c_69,c_141])).

tff(c_149,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_10])).

tff(c_201,plain,(
    ! [D_101,C_102,A_103,B_104] :
      ( D_101 = C_102
      | ~ r2_hidden(k4_tarski(D_101,C_102),A_103)
      | ~ r2_hidden(k4_tarski(C_102,D_101),A_103)
      | ~ r2_hidden(D_101,B_104)
      | ~ r2_hidden(C_102,B_104)
      | ~ r4_relat_2(A_103,B_104)
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_315,plain,(
    ! [C_160,B_161,A_162,B_163] :
      ( C_160 = B_161
      | ~ r2_hidden(k4_tarski(C_160,B_161),u1_orders_2(A_162))
      | ~ r2_hidden(B_161,B_163)
      | ~ r2_hidden(C_160,B_163)
      | ~ r4_relat_2(u1_orders_2(A_162),B_163)
      | ~ v1_relat_1(u1_orders_2(A_162))
      | ~ r1_orders_2(A_162,B_161,C_160)
      | ~ m1_subset_1(C_160,u1_struct_0(A_162))
      | ~ m1_subset_1(B_161,u1_struct_0(A_162))
      | ~ l1_orders_2(A_162) ) ),
    inference(resolution,[status(thm)],[c_38,c_201])).

tff(c_331,plain,(
    ! [C_164,B_165,B_166,A_167] :
      ( C_164 = B_165
      | ~ r2_hidden(C_164,B_166)
      | ~ r2_hidden(B_165,B_166)
      | ~ r4_relat_2(u1_orders_2(A_167),B_166)
      | ~ v1_relat_1(u1_orders_2(A_167))
      | ~ r1_orders_2(A_167,C_164,B_165)
      | ~ r1_orders_2(A_167,B_165,C_164)
      | ~ m1_subset_1(C_164,u1_struct_0(A_167))
      | ~ m1_subset_1(B_165,u1_struct_0(A_167))
      | ~ l1_orders_2(A_167) ) ),
    inference(resolution,[status(thm)],[c_38,c_315])).

tff(c_350,plain,(
    ! [B_168,A_169,B_170,A_171] :
      ( B_168 = A_169
      | ~ r2_hidden(B_168,B_170)
      | ~ r4_relat_2(u1_orders_2(A_171),B_170)
      | ~ v1_relat_1(u1_orders_2(A_171))
      | ~ r1_orders_2(A_171,A_169,B_168)
      | ~ r1_orders_2(A_171,B_168,A_169)
      | ~ m1_subset_1(A_169,u1_struct_0(A_171))
      | ~ m1_subset_1(B_168,u1_struct_0(A_171))
      | ~ l1_orders_2(A_171)
      | ~ m1_subset_1(A_169,B_170) ) ),
    inference(resolution,[status(thm)],[c_149,c_331])).

tff(c_369,plain,(
    ! [A_173,A_172,A_174,B_175] :
      ( A_173 = A_172
      | ~ r4_relat_2(u1_orders_2(A_174),B_175)
      | ~ v1_relat_1(u1_orders_2(A_174))
      | ~ r1_orders_2(A_174,A_173,A_172)
      | ~ r1_orders_2(A_174,A_172,A_173)
      | ~ m1_subset_1(A_173,u1_struct_0(A_174))
      | ~ m1_subset_1(A_172,u1_struct_0(A_174))
      | ~ l1_orders_2(A_174)
      | ~ m1_subset_1(A_173,B_175)
      | ~ m1_subset_1(A_172,B_175) ) ),
    inference(resolution,[status(thm)],[c_149,c_350])).

tff(c_377,plain,(
    ! [A_177,A_176,A_178] :
      ( A_177 = A_176
      | ~ v1_relat_1(u1_orders_2(A_178))
      | ~ r1_orders_2(A_178,A_176,A_177)
      | ~ r1_orders_2(A_178,A_177,A_176)
      | ~ m1_subset_1(A_176,u1_struct_0(A_178))
      | ~ m1_subset_1(A_177,u1_struct_0(A_178))
      | ~ v5_orders_2(A_178)
      | ~ l1_orders_2(A_178) ) ),
    inference(resolution,[status(thm)],[c_34,c_369])).

tff(c_383,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_4'))
    | ~ r1_orders_2('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v5_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_377])).

tff(c_390,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_50,c_48,c_46,c_383])).

tff(c_391,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_390])).

tff(c_417,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_170,c_391])).

tff(c_421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_417])).

tff(c_422,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_74,plain,(
    ! [A_61] :
      ( '#skF_1'(A_61) = k1_xboole_0
      | ~ v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_429,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_422,c_74])).

tff(c_112,plain,(
    ! [C_67,B_68,A_69] :
      ( ~ v1_xboole_0(C_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(C_67))
      | ~ r2_hidden(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_115,plain,(
    ! [A_5,A_69] :
      ( ~ v1_xboole_0(A_5)
      | ~ r2_hidden(A_69,'#skF_1'(A_5)) ) ),
    inference(resolution,[status(thm)],[c_8,c_112])).

tff(c_438,plain,(
    ! [A_69] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_69,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_115])).

tff(c_462,plain,(
    ! [A_69] : ~ r2_hidden(A_69,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_438])).

tff(c_18,plain,(
    ! [C_20,B_18,A_17] :
      ( v1_xboole_0(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(B_18,A_17)))
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_799,plain,(
    ! [A_222] :
      ( v1_xboole_0(u1_orders_2(A_222))
      | ~ v1_xboole_0(u1_struct_0(A_222))
      | ~ l1_orders_2(A_222) ) ),
    inference(resolution,[status(thm)],[c_787,c_18])).

tff(c_1144,plain,
    ( v1_xboole_0(u1_orders_2('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_1140,c_799])).

tff(c_1153,plain,(
    v1_xboole_0(u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1144])).

tff(c_1219,plain,(
    u1_orders_2('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1153,c_2])).

tff(c_1252,plain,(
    ! [B_43,C_45] :
      ( r2_hidden(k4_tarski(B_43,C_45),k1_xboole_0)
      | ~ r1_orders_2('#skF_4',B_43,C_45)
      | ~ m1_subset_1(C_45,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1219,c_38])).

tff(c_1287,plain,(
    ! [B_43,C_45] :
      ( r2_hidden(k4_tarski(B_43,C_45),k1_xboole_0)
      | ~ r1_orders_2('#skF_4',B_43,C_45)
      | ~ m1_subset_1(C_45,k1_xboole_0)
      | ~ m1_subset_1(B_43,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1155,c_1155,c_1252])).

tff(c_1329,plain,(
    ! [B_326,C_327] :
      ( ~ r1_orders_2('#skF_4',B_326,C_327)
      | ~ m1_subset_1(C_327,k1_xboole_0)
      | ~ m1_subset_1(B_326,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_462,c_1287])).

tff(c_1340,plain,
    ( ~ m1_subset_1('#skF_5',k1_xboole_0)
    | ~ m1_subset_1('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_44,c_1329])).

tff(c_1353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1158,c_1157,c_1340])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:54:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.29/1.78  
% 4.29/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.29/1.78  %$ r1_orders_2 > v1_subset_1 > r4_relat_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 4.29/1.78  
% 4.29/1.78  %Foreground sorts:
% 4.29/1.78  
% 4.29/1.78  
% 4.29/1.78  %Background operators:
% 4.29/1.78  
% 4.29/1.78  
% 4.29/1.78  %Foreground operators:
% 4.29/1.78  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 4.29/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.29/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.29/1.78  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.29/1.78  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.29/1.78  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.29/1.78  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.29/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.29/1.78  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.29/1.78  tff('#skF_5', type, '#skF_5': $i).
% 4.29/1.78  tff('#skF_6', type, '#skF_6': $i).
% 4.29/1.78  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.29/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.29/1.78  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.29/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.29/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.29/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.29/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.29/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.29/1.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.29/1.78  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 4.29/1.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.29/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.29/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.29/1.78  
% 4.35/1.80  tff(f_126, negated_conjecture, ~(![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_orders_2)).
% 4.35/1.80  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.35/1.80  tff(f_109, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 4.35/1.80  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.35/1.80  tff(f_93, axiom, (![A]: (l1_orders_2(A) => (v5_orders_2(A) <=> r4_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_orders_2)).
% 4.35/1.80  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.35/1.80  tff(f_105, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 4.35/1.80  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (![B]: (r4_relat_2(A, B) <=> (![C, D]: ((((r2_hidden(C, B) & r2_hidden(D, B)) & r2_hidden(k4_tarski(C, D), A)) & r2_hidden(k4_tarski(D, C), A)) => (C = D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_2)).
% 4.35/1.80  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.35/1.80  tff(f_42, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 4.35/1.80  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.35/1.80  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.35/1.80  tff(f_71, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.35/1.80  tff(c_52, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.35/1.80  tff(c_16, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.35/1.80  tff(c_787, plain, (![A_222]: (m1_subset_1(u1_orders_2(A_222), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_222), u1_struct_0(A_222)))) | ~l1_orders_2(A_222))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.35/1.80  tff(c_14, plain, (![B_14, A_12]: (v1_relat_1(B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_12)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.35/1.80  tff(c_798, plain, (![A_222]: (v1_relat_1(u1_orders_2(A_222)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_222), u1_struct_0(A_222))) | ~l1_orders_2(A_222))), inference(resolution, [status(thm)], [c_787, c_14])).
% 4.35/1.80  tff(c_804, plain, (![A_222]: (v1_relat_1(u1_orders_2(A_222)) | ~l1_orders_2(A_222))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_798])).
% 4.35/1.80  tff(c_42, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.35/1.80  tff(c_54, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.35/1.80  tff(c_50, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.35/1.80  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.35/1.80  tff(c_46, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.35/1.80  tff(c_44, plain, (r1_orders_2('#skF_4', '#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.35/1.80  tff(c_34, plain, (![A_38]: (r4_relat_2(u1_orders_2(A_38), u1_struct_0(A_38)) | ~v5_orders_2(A_38) | ~l1_orders_2(A_38))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.35/1.80  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.35/1.80  tff(c_38, plain, (![B_43, C_45, A_39]: (r2_hidden(k4_tarski(B_43, C_45), u1_orders_2(A_39)) | ~r1_orders_2(A_39, B_43, C_45) | ~m1_subset_1(C_45, u1_struct_0(A_39)) | ~m1_subset_1(B_43, u1_struct_0(A_39)) | ~l1_orders_2(A_39))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.35/1.80  tff(c_894, plain, (![D_244, C_245, A_246, B_247]: (D_244=C_245 | ~r2_hidden(k4_tarski(D_244, C_245), A_246) | ~r2_hidden(k4_tarski(C_245, D_244), A_246) | ~r2_hidden(D_244, B_247) | ~r2_hidden(C_245, B_247) | ~r4_relat_2(A_246, B_247) | ~v1_relat_1(A_246))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.35/1.80  tff(c_1021, plain, (![C_295, B_296, A_297, B_298]: (C_295=B_296 | ~r2_hidden(k4_tarski(C_295, B_296), u1_orders_2(A_297)) | ~r2_hidden(B_296, B_298) | ~r2_hidden(C_295, B_298) | ~r4_relat_2(u1_orders_2(A_297), B_298) | ~v1_relat_1(u1_orders_2(A_297)) | ~r1_orders_2(A_297, B_296, C_295) | ~m1_subset_1(C_295, u1_struct_0(A_297)) | ~m1_subset_1(B_296, u1_struct_0(A_297)) | ~l1_orders_2(A_297))), inference(resolution, [status(thm)], [c_38, c_894])).
% 4.35/1.80  tff(c_1037, plain, (![C_299, B_300, B_301, A_302]: (C_299=B_300 | ~r2_hidden(C_299, B_301) | ~r2_hidden(B_300, B_301) | ~r4_relat_2(u1_orders_2(A_302), B_301) | ~v1_relat_1(u1_orders_2(A_302)) | ~r1_orders_2(A_302, C_299, B_300) | ~r1_orders_2(A_302, B_300, C_299) | ~m1_subset_1(C_299, u1_struct_0(A_302)) | ~m1_subset_1(B_300, u1_struct_0(A_302)) | ~l1_orders_2(A_302))), inference(resolution, [status(thm)], [c_38, c_1021])).
% 4.35/1.80  tff(c_1056, plain, (![B_303, A_304, B_305, A_306]: (B_303=A_304 | ~r2_hidden(B_303, B_305) | ~r4_relat_2(u1_orders_2(A_306), B_305) | ~v1_relat_1(u1_orders_2(A_306)) | ~r1_orders_2(A_306, A_304, B_303) | ~r1_orders_2(A_306, B_303, A_304) | ~m1_subset_1(A_304, u1_struct_0(A_306)) | ~m1_subset_1(B_303, u1_struct_0(A_306)) | ~l1_orders_2(A_306) | v1_xboole_0(B_305) | ~m1_subset_1(A_304, B_305))), inference(resolution, [status(thm)], [c_10, c_1037])).
% 4.35/1.80  tff(c_1096, plain, (![A_320, A_319, A_321, B_322]: (A_320=A_319 | ~r4_relat_2(u1_orders_2(A_321), B_322) | ~v1_relat_1(u1_orders_2(A_321)) | ~r1_orders_2(A_321, A_320, A_319) | ~r1_orders_2(A_321, A_319, A_320) | ~m1_subset_1(A_320, u1_struct_0(A_321)) | ~m1_subset_1(A_319, u1_struct_0(A_321)) | ~l1_orders_2(A_321) | ~m1_subset_1(A_320, B_322) | v1_xboole_0(B_322) | ~m1_subset_1(A_319, B_322))), inference(resolution, [status(thm)], [c_10, c_1056])).
% 4.35/1.80  tff(c_1113, plain, (![A_324, A_323, A_325]: (A_324=A_323 | ~v1_relat_1(u1_orders_2(A_325)) | ~r1_orders_2(A_325, A_323, A_324) | ~r1_orders_2(A_325, A_324, A_323) | ~m1_subset_1(A_323, u1_struct_0(A_325)) | v1_xboole_0(u1_struct_0(A_325)) | ~m1_subset_1(A_324, u1_struct_0(A_325)) | ~v5_orders_2(A_325) | ~l1_orders_2(A_325))), inference(resolution, [status(thm)], [c_34, c_1096])).
% 4.35/1.80  tff(c_1119, plain, ('#skF_5'='#skF_6' | ~v1_relat_1(u1_orders_2('#skF_4')) | ~r1_orders_2('#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v5_orders_2('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1113])).
% 4.35/1.80  tff(c_1126, plain, ('#skF_5'='#skF_6' | ~v1_relat_1(u1_orders_2('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_50, c_48, c_46, c_1119])).
% 4.35/1.80  tff(c_1127, plain, (~v1_relat_1(u1_orders_2('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_1126])).
% 4.35/1.80  tff(c_1132, plain, (~v1_relat_1(u1_orders_2('#skF_4'))), inference(splitLeft, [status(thm)], [c_1127])).
% 4.35/1.80  tff(c_1135, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_804, c_1132])).
% 4.35/1.80  tff(c_1139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1135])).
% 4.35/1.80  tff(c_1140, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1127])).
% 4.35/1.80  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.35/1.80  tff(c_1155, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1140, c_2])).
% 4.35/1.80  tff(c_1158, plain, (m1_subset_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1155, c_48])).
% 4.35/1.80  tff(c_1157, plain, (m1_subset_1('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1155, c_50])).
% 4.35/1.80  tff(c_164, plain, (![A_83]: (m1_subset_1(u1_orders_2(A_83), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_83), u1_struct_0(A_83)))) | ~l1_orders_2(A_83))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.35/1.80  tff(c_167, plain, (![A_83]: (v1_relat_1(u1_orders_2(A_83)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_83), u1_struct_0(A_83))) | ~l1_orders_2(A_83))), inference(resolution, [status(thm)], [c_164, c_14])).
% 4.35/1.80  tff(c_170, plain, (![A_83]: (v1_relat_1(u1_orders_2(A_83)) | ~l1_orders_2(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_167])).
% 4.35/1.80  tff(c_8, plain, (![A_5]: (m1_subset_1('#skF_1'(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.35/1.80  tff(c_65, plain, (![B_59, A_60]: (v1_xboole_0(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.35/1.80  tff(c_69, plain, (![A_5]: (v1_xboole_0('#skF_1'(A_5)) | ~v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_8, c_65])).
% 4.35/1.80  tff(c_70, plain, (![A_61]: (v1_xboole_0('#skF_1'(A_61)) | ~v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_8, c_65])).
% 4.35/1.80  tff(c_76, plain, (![A_64]: ('#skF_1'(A_64)=k1_xboole_0 | ~v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_70, c_2])).
% 4.35/1.80  tff(c_81, plain, (![A_65]: ('#skF_1'('#skF_1'(A_65))=k1_xboole_0 | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_69, c_76])).
% 4.35/1.80  tff(c_90, plain, (![A_65]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0('#skF_1'(A_65)) | ~v1_xboole_0(A_65))), inference(superposition, [status(thm), theory('equality')], [c_81, c_69])).
% 4.35/1.80  tff(c_141, plain, (![A_73]: (~v1_xboole_0('#skF_1'(A_73)) | ~v1_xboole_0(A_73))), inference(splitLeft, [status(thm)], [c_90])).
% 4.35/1.80  tff(c_148, plain, (![A_5]: (~v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_69, c_141])).
% 4.35/1.80  tff(c_149, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | ~m1_subset_1(A_7, B_8))), inference(negUnitSimplification, [status(thm)], [c_148, c_10])).
% 4.35/1.80  tff(c_201, plain, (![D_101, C_102, A_103, B_104]: (D_101=C_102 | ~r2_hidden(k4_tarski(D_101, C_102), A_103) | ~r2_hidden(k4_tarski(C_102, D_101), A_103) | ~r2_hidden(D_101, B_104) | ~r2_hidden(C_102, B_104) | ~r4_relat_2(A_103, B_104) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.35/1.80  tff(c_315, plain, (![C_160, B_161, A_162, B_163]: (C_160=B_161 | ~r2_hidden(k4_tarski(C_160, B_161), u1_orders_2(A_162)) | ~r2_hidden(B_161, B_163) | ~r2_hidden(C_160, B_163) | ~r4_relat_2(u1_orders_2(A_162), B_163) | ~v1_relat_1(u1_orders_2(A_162)) | ~r1_orders_2(A_162, B_161, C_160) | ~m1_subset_1(C_160, u1_struct_0(A_162)) | ~m1_subset_1(B_161, u1_struct_0(A_162)) | ~l1_orders_2(A_162))), inference(resolution, [status(thm)], [c_38, c_201])).
% 4.35/1.80  tff(c_331, plain, (![C_164, B_165, B_166, A_167]: (C_164=B_165 | ~r2_hidden(C_164, B_166) | ~r2_hidden(B_165, B_166) | ~r4_relat_2(u1_orders_2(A_167), B_166) | ~v1_relat_1(u1_orders_2(A_167)) | ~r1_orders_2(A_167, C_164, B_165) | ~r1_orders_2(A_167, B_165, C_164) | ~m1_subset_1(C_164, u1_struct_0(A_167)) | ~m1_subset_1(B_165, u1_struct_0(A_167)) | ~l1_orders_2(A_167))), inference(resolution, [status(thm)], [c_38, c_315])).
% 4.35/1.80  tff(c_350, plain, (![B_168, A_169, B_170, A_171]: (B_168=A_169 | ~r2_hidden(B_168, B_170) | ~r4_relat_2(u1_orders_2(A_171), B_170) | ~v1_relat_1(u1_orders_2(A_171)) | ~r1_orders_2(A_171, A_169, B_168) | ~r1_orders_2(A_171, B_168, A_169) | ~m1_subset_1(A_169, u1_struct_0(A_171)) | ~m1_subset_1(B_168, u1_struct_0(A_171)) | ~l1_orders_2(A_171) | ~m1_subset_1(A_169, B_170))), inference(resolution, [status(thm)], [c_149, c_331])).
% 4.35/1.80  tff(c_369, plain, (![A_173, A_172, A_174, B_175]: (A_173=A_172 | ~r4_relat_2(u1_orders_2(A_174), B_175) | ~v1_relat_1(u1_orders_2(A_174)) | ~r1_orders_2(A_174, A_173, A_172) | ~r1_orders_2(A_174, A_172, A_173) | ~m1_subset_1(A_173, u1_struct_0(A_174)) | ~m1_subset_1(A_172, u1_struct_0(A_174)) | ~l1_orders_2(A_174) | ~m1_subset_1(A_173, B_175) | ~m1_subset_1(A_172, B_175))), inference(resolution, [status(thm)], [c_149, c_350])).
% 4.35/1.80  tff(c_377, plain, (![A_177, A_176, A_178]: (A_177=A_176 | ~v1_relat_1(u1_orders_2(A_178)) | ~r1_orders_2(A_178, A_176, A_177) | ~r1_orders_2(A_178, A_177, A_176) | ~m1_subset_1(A_176, u1_struct_0(A_178)) | ~m1_subset_1(A_177, u1_struct_0(A_178)) | ~v5_orders_2(A_178) | ~l1_orders_2(A_178))), inference(resolution, [status(thm)], [c_34, c_369])).
% 4.35/1.80  tff(c_383, plain, ('#skF_5'='#skF_6' | ~v1_relat_1(u1_orders_2('#skF_4')) | ~r1_orders_2('#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v5_orders_2('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_44, c_377])).
% 4.35/1.80  tff(c_390, plain, ('#skF_5'='#skF_6' | ~v1_relat_1(u1_orders_2('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_50, c_48, c_46, c_383])).
% 4.35/1.80  tff(c_391, plain, (~v1_relat_1(u1_orders_2('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_390])).
% 4.35/1.80  tff(c_417, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_170, c_391])).
% 4.35/1.80  tff(c_421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_417])).
% 4.35/1.80  tff(c_422, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_90])).
% 4.35/1.80  tff(c_74, plain, (![A_61]: ('#skF_1'(A_61)=k1_xboole_0 | ~v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_70, c_2])).
% 4.35/1.80  tff(c_429, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_422, c_74])).
% 4.35/1.80  tff(c_112, plain, (![C_67, B_68, A_69]: (~v1_xboole_0(C_67) | ~m1_subset_1(B_68, k1_zfmisc_1(C_67)) | ~r2_hidden(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.35/1.80  tff(c_115, plain, (![A_5, A_69]: (~v1_xboole_0(A_5) | ~r2_hidden(A_69, '#skF_1'(A_5)))), inference(resolution, [status(thm)], [c_8, c_112])).
% 4.35/1.80  tff(c_438, plain, (![A_69]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_69, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_429, c_115])).
% 4.35/1.80  tff(c_462, plain, (![A_69]: (~r2_hidden(A_69, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_438])).
% 4.35/1.80  tff(c_18, plain, (![C_20, B_18, A_17]: (v1_xboole_0(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(B_18, A_17))) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.35/1.80  tff(c_799, plain, (![A_222]: (v1_xboole_0(u1_orders_2(A_222)) | ~v1_xboole_0(u1_struct_0(A_222)) | ~l1_orders_2(A_222))), inference(resolution, [status(thm)], [c_787, c_18])).
% 4.35/1.80  tff(c_1144, plain, (v1_xboole_0(u1_orders_2('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_1140, c_799])).
% 4.35/1.80  tff(c_1153, plain, (v1_xboole_0(u1_orders_2('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1144])).
% 4.35/1.80  tff(c_1219, plain, (u1_orders_2('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1153, c_2])).
% 4.35/1.80  tff(c_1252, plain, (![B_43, C_45]: (r2_hidden(k4_tarski(B_43, C_45), k1_xboole_0) | ~r1_orders_2('#skF_4', B_43, C_45) | ~m1_subset_1(C_45, u1_struct_0('#skF_4')) | ~m1_subset_1(B_43, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1219, c_38])).
% 4.35/1.80  tff(c_1287, plain, (![B_43, C_45]: (r2_hidden(k4_tarski(B_43, C_45), k1_xboole_0) | ~r1_orders_2('#skF_4', B_43, C_45) | ~m1_subset_1(C_45, k1_xboole_0) | ~m1_subset_1(B_43, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1155, c_1155, c_1252])).
% 4.35/1.80  tff(c_1329, plain, (![B_326, C_327]: (~r1_orders_2('#skF_4', B_326, C_327) | ~m1_subset_1(C_327, k1_xboole_0) | ~m1_subset_1(B_326, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_462, c_1287])).
% 4.35/1.80  tff(c_1340, plain, (~m1_subset_1('#skF_5', k1_xboole_0) | ~m1_subset_1('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_1329])).
% 4.35/1.80  tff(c_1353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1158, c_1157, c_1340])).
% 4.35/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.80  
% 4.35/1.80  Inference rules
% 4.35/1.80  ----------------------
% 4.35/1.80  #Ref     : 0
% 4.35/1.80  #Sup     : 293
% 4.35/1.80  #Fact    : 0
% 4.35/1.80  #Define  : 0
% 4.35/1.80  #Split   : 3
% 4.35/1.80  #Chain   : 0
% 4.35/1.80  #Close   : 0
% 4.35/1.80  
% 4.35/1.80  Ordering : KBO
% 4.35/1.80  
% 4.35/1.80  Simplification rules
% 4.35/1.80  ----------------------
% 4.35/1.80  #Subsume      : 86
% 4.35/1.80  #Demod        : 243
% 4.35/1.80  #Tautology    : 94
% 4.35/1.80  #SimpNegUnit  : 18
% 4.35/1.80  #BackRed      : 8
% 4.35/1.80  
% 4.35/1.80  #Partial instantiations: 0
% 4.35/1.80  #Strategies tried      : 1
% 4.35/1.80  
% 4.35/1.80  Timing (in seconds)
% 4.35/1.80  ----------------------
% 4.35/1.80  Preprocessing        : 0.34
% 4.35/1.80  Parsing              : 0.18
% 4.35/1.80  CNF conversion       : 0.03
% 4.35/1.80  Main loop            : 0.63
% 4.35/1.80  Inferencing          : 0.22
% 4.35/1.80  Reduction            : 0.17
% 4.35/1.80  Demodulation         : 0.11
% 4.35/1.81  BG Simplification    : 0.03
% 4.35/1.81  Subsumption          : 0.16
% 4.35/1.81  Abstraction          : 0.03
% 4.35/1.81  MUC search           : 0.00
% 4.35/1.81  Cooper               : 0.00
% 4.35/1.81  Total                : 1.01
% 4.35/1.81  Index Insertion      : 0.00
% 4.35/1.81  Index Deletion       : 0.00
% 4.35/1.81  Index Matching       : 0.00
% 4.35/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
