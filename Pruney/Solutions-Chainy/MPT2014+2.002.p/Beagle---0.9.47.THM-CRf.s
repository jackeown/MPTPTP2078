%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:09 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 135 expanded)
%              Number of leaves         :   39 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :  210 ( 510 expanded)
%              Number of equality atoms :    5 (  16 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_orders_2 > v6_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > k2_partfun1 > k4_waybel_9 > u1_waybel_0 > k2_zfmisc_1 > k1_toler_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_7 > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(v6_waybel_0,type,(
    v6_waybel_0: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k4_waybel_9,type,(
    k4_waybel_9: ( $i * $i * $i ) > $i )).

tff(k1_toler_1,type,(
    k1_toler_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

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

tff(f_140,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => r1_tarski(u1_struct_0(k4_waybel_9(A,B,C)),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_9)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( v6_waybel_0(k4_waybel_9(A,B,C),A)
        & l1_waybel_0(k4_waybel_9(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => ! [D] :
                  ( ( v6_waybel_0(D,A)
                    & l1_waybel_0(D,A) )
                 => ( D = k4_waybel_9(A,B,C)
                  <=> ( ! [E] :
                          ( r2_hidden(E,u1_struct_0(D))
                        <=> ? [F] :
                              ( m1_subset_1(F,u1_struct_0(B))
                              & F = E
                              & r1_orders_2(B,C,F) ) )
                      & r2_relset_1(u1_struct_0(D),u1_struct_0(D),u1_orders_2(D),k1_toler_1(u1_orders_2(B),u1_struct_0(D)))
                      & u1_waybel_0(A,D) = k2_partfun1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B),u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_9)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(u1_waybel_0(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & ~ v1_xboole_0(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc15_yellow_6)).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_64,plain,(
    l1_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_60,plain,(
    l1_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_58,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_121,plain,(
    ! [A_232,B_233,C_234] :
      ( l1_waybel_0(k4_waybel_9(A_232,B_233,C_234),A_232)
      | ~ m1_subset_1(C_234,u1_struct_0(B_233))
      | ~ l1_waybel_0(B_233,A_232)
      | v2_struct_0(B_233)
      | ~ l1_struct_0(A_232)
      | v2_struct_0(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_123,plain,(
    ! [A_232] :
      ( l1_waybel_0(k4_waybel_9(A_232,'#skF_7','#skF_8'),A_232)
      | ~ l1_waybel_0('#skF_7',A_232)
      | v2_struct_0('#skF_7')
      | ~ l1_struct_0(A_232)
      | v2_struct_0(A_232) ) ),
    inference(resolution,[status(thm)],[c_58,c_121])).

tff(c_126,plain,(
    ! [A_232] :
      ( l1_waybel_0(k4_waybel_9(A_232,'#skF_7','#skF_8'),A_232)
      | ~ l1_waybel_0('#skF_7',A_232)
      | ~ l1_struct_0(A_232)
      | v2_struct_0(A_232) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_123])).

tff(c_54,plain,(
    ! [A_188,B_189,C_190] :
      ( v6_waybel_0(k4_waybel_9(A_188,B_189,C_190),A_188)
      | ~ m1_subset_1(C_190,u1_struct_0(B_189))
      | ~ l1_waybel_0(B_189,A_188)
      | v2_struct_0(B_189)
      | ~ l1_struct_0(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_155,plain,(
    ! [C_254,A_255,B_256,E_257] :
      ( '#skF_2'(C_254,A_255,B_256,E_257,k4_waybel_9(A_255,B_256,C_254)) = E_257
      | ~ r2_hidden(E_257,u1_struct_0(k4_waybel_9(A_255,B_256,C_254)))
      | ~ l1_waybel_0(k4_waybel_9(A_255,B_256,C_254),A_255)
      | ~ v6_waybel_0(k4_waybel_9(A_255,B_256,C_254),A_255)
      | ~ m1_subset_1(C_254,u1_struct_0(B_256))
      | ~ l1_waybel_0(B_256,A_255)
      | v2_struct_0(B_256)
      | ~ l1_struct_0(A_255)
      | v2_struct_0(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_281,plain,(
    ! [C_306,A_307,B_308,B_309] :
      ( '#skF_2'(C_306,A_307,B_308,'#skF_1'(u1_struct_0(k4_waybel_9(A_307,B_308,C_306)),B_309),k4_waybel_9(A_307,B_308,C_306)) = '#skF_1'(u1_struct_0(k4_waybel_9(A_307,B_308,C_306)),B_309)
      | ~ l1_waybel_0(k4_waybel_9(A_307,B_308,C_306),A_307)
      | ~ v6_waybel_0(k4_waybel_9(A_307,B_308,C_306),A_307)
      | ~ m1_subset_1(C_306,u1_struct_0(B_308))
      | ~ l1_waybel_0(B_308,A_307)
      | v2_struct_0(B_308)
      | ~ l1_struct_0(A_307)
      | v2_struct_0(A_307)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_307,B_308,C_306)),B_309) ) ),
    inference(resolution,[status(thm)],[c_6,c_155])).

tff(c_50,plain,(
    ! [C_148,A_16,B_104,E_181] :
      ( m1_subset_1('#skF_2'(C_148,A_16,B_104,E_181,k4_waybel_9(A_16,B_104,C_148)),u1_struct_0(B_104))
      | ~ r2_hidden(E_181,u1_struct_0(k4_waybel_9(A_16,B_104,C_148)))
      | ~ l1_waybel_0(k4_waybel_9(A_16,B_104,C_148),A_16)
      | ~ v6_waybel_0(k4_waybel_9(A_16,B_104,C_148),A_16)
      | ~ m1_subset_1(C_148,u1_struct_0(B_104))
      | ~ l1_waybel_0(B_104,A_16)
      | v2_struct_0(B_104)
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_346,plain,(
    ! [A_346,B_347,C_348,B_349] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_346,B_347,C_348)),B_349),u1_struct_0(B_347))
      | ~ r2_hidden('#skF_1'(u1_struct_0(k4_waybel_9(A_346,B_347,C_348)),B_349),u1_struct_0(k4_waybel_9(A_346,B_347,C_348)))
      | ~ l1_waybel_0(k4_waybel_9(A_346,B_347,C_348),A_346)
      | ~ v6_waybel_0(k4_waybel_9(A_346,B_347,C_348),A_346)
      | ~ m1_subset_1(C_348,u1_struct_0(B_347))
      | ~ l1_waybel_0(B_347,A_346)
      | v2_struct_0(B_347)
      | ~ l1_struct_0(A_346)
      | v2_struct_0(A_346)
      | ~ l1_waybel_0(k4_waybel_9(A_346,B_347,C_348),A_346)
      | ~ v6_waybel_0(k4_waybel_9(A_346,B_347,C_348),A_346)
      | ~ m1_subset_1(C_348,u1_struct_0(B_347))
      | ~ l1_waybel_0(B_347,A_346)
      | v2_struct_0(B_347)
      | ~ l1_struct_0(A_346)
      | v2_struct_0(A_346)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_346,B_347,C_348)),B_349) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_50])).

tff(c_388,plain,(
    ! [A_355,B_356,C_357,B_358] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_355,B_356,C_357)),B_358),u1_struct_0(B_356))
      | ~ l1_waybel_0(k4_waybel_9(A_355,B_356,C_357),A_355)
      | ~ v6_waybel_0(k4_waybel_9(A_355,B_356,C_357),A_355)
      | ~ m1_subset_1(C_357,u1_struct_0(B_356))
      | ~ l1_waybel_0(B_356,A_355)
      | v2_struct_0(B_356)
      | ~ l1_struct_0(A_355)
      | v2_struct_0(A_355)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_355,B_356,C_357)),B_358) ) ),
    inference(resolution,[status(thm)],[c_6,c_346])).

tff(c_392,plain,(
    ! [A_359,B_360,C_361,B_362] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_359,B_360,C_361)),B_362),u1_struct_0(B_360))
      | ~ l1_waybel_0(k4_waybel_9(A_359,B_360,C_361),A_359)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_359,B_360,C_361)),B_362)
      | ~ m1_subset_1(C_361,u1_struct_0(B_360))
      | ~ l1_waybel_0(B_360,A_359)
      | v2_struct_0(B_360)
      | ~ l1_struct_0(A_359)
      | v2_struct_0(A_359) ) ),
    inference(resolution,[status(thm)],[c_54,c_388])).

tff(c_396,plain,(
    ! [A_232,B_362] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_232,'#skF_7','#skF_8')),B_362),u1_struct_0('#skF_7'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_232,'#skF_7','#skF_8')),B_362)
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0('#skF_7',A_232)
      | ~ l1_struct_0(A_232)
      | v2_struct_0(A_232) ) ),
    inference(resolution,[status(thm)],[c_126,c_392])).

tff(c_400,plain,(
    ! [A_232,B_362] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_232,'#skF_7','#skF_8')),B_362),u1_struct_0('#skF_7'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_232,'#skF_7','#skF_8')),B_362)
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0('#skF_7',A_232)
      | ~ l1_struct_0(A_232)
      | v2_struct_0(A_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_396])).

tff(c_402,plain,(
    ! [A_363,B_364] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_363,'#skF_7','#skF_8')),B_364),u1_struct_0('#skF_7'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_363,'#skF_7','#skF_8')),B_364)
      | ~ l1_waybel_0('#skF_7',A_363)
      | ~ l1_struct_0(A_363)
      | v2_struct_0(A_363) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_400])).

tff(c_75,plain,(
    ! [A_200,B_201] :
      ( r2_hidden(A_200,B_201)
      | v1_xboole_0(B_201)
      | ~ m1_subset_1(A_200,B_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_1,B_201] :
      ( r1_tarski(A_1,B_201)
      | v1_xboole_0(B_201)
      | ~ m1_subset_1('#skF_1'(A_1,B_201),B_201) ) ),
    inference(resolution,[status(thm)],[c_75,c_4])).

tff(c_420,plain,(
    ! [A_363] :
      ( v1_xboole_0(u1_struct_0('#skF_7'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_363,'#skF_7','#skF_8')),u1_struct_0('#skF_7'))
      | ~ l1_waybel_0('#skF_7',A_363)
      | ~ l1_struct_0(A_363)
      | v2_struct_0(A_363) ) ),
    inference(resolution,[status(thm)],[c_402,c_80])).

tff(c_421,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_420])).

tff(c_110,plain,(
    ! [A_226,B_227] :
      ( m1_subset_1(u1_waybel_0(A_226,B_227),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_227),u1_struct_0(A_226))))
      | ~ l1_waybel_0(B_227,A_226)
      | ~ l1_struct_0(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [C_11,A_8,B_9] :
      ( v1_xboole_0(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_115,plain,(
    ! [A_228,B_229] :
      ( v1_xboole_0(u1_waybel_0(A_228,B_229))
      | ~ v1_xboole_0(u1_struct_0(B_229))
      | ~ l1_waybel_0(B_229,A_228)
      | ~ l1_struct_0(A_228) ) ),
    inference(resolution,[status(thm)],[c_110,c_10])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( ~ v1_xboole_0(u1_waybel_0(A_14,B_15))
      | ~ l1_waybel_0(B_15,A_14)
      | v2_struct_0(B_15)
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_119,plain,(
    ! [B_229,A_228] :
      ( v2_struct_0(B_229)
      | v2_struct_0(A_228)
      | ~ v1_xboole_0(u1_struct_0(B_229))
      | ~ l1_waybel_0(B_229,A_228)
      | ~ l1_struct_0(A_228) ) ),
    inference(resolution,[status(thm)],[c_115,c_20])).

tff(c_423,plain,(
    ! [A_228] :
      ( v2_struct_0('#skF_7')
      | v2_struct_0(A_228)
      | ~ l1_waybel_0('#skF_7',A_228)
      | ~ l1_struct_0(A_228) ) ),
    inference(resolution,[status(thm)],[c_421,c_119])).

tff(c_431,plain,(
    ! [A_369] :
      ( v2_struct_0(A_369)
      | ~ l1_waybel_0('#skF_7',A_369)
      | ~ l1_struct_0(A_369) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_423])).

tff(c_434,plain,
    ( v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_431])).

tff(c_437,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_434])).

tff(c_439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_437])).

tff(c_442,plain,(
    ! [A_370] :
      ( r1_tarski(u1_struct_0(k4_waybel_9(A_370,'#skF_7','#skF_8')),u1_struct_0('#skF_7'))
      | ~ l1_waybel_0('#skF_7',A_370)
      | ~ l1_struct_0(A_370)
      | v2_struct_0(A_370) ) ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_56,plain,(
    ~ r1_tarski(u1_struct_0(k4_waybel_9('#skF_6','#skF_7','#skF_8')),u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_451,plain,
    ( ~ l1_waybel_0('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_442,c_56])).

tff(c_457,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_451])).

tff(c_459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_457])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:15:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.51  
% 3.14/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.52  %$ r2_relset_1 > v1_funct_2 > r1_orders_2 > v6_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > k2_partfun1 > k4_waybel_9 > u1_waybel_0 > k2_zfmisc_1 > k1_toler_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_7 > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 3.14/1.52  
% 3.14/1.52  %Foreground sorts:
% 3.14/1.52  
% 3.14/1.52  
% 3.14/1.52  %Background operators:
% 3.14/1.52  
% 3.14/1.52  
% 3.14/1.52  %Foreground operators:
% 3.14/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.14/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.14/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.52  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.14/1.52  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 3.14/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 3.14/1.52  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.14/1.52  tff(k4_waybel_9, type, k4_waybel_9: ($i * $i * $i) > $i).
% 3.14/1.52  tff(k1_toler_1, type, k1_toler_1: ($i * $i) > $i).
% 3.14/1.52  tff('#skF_7', type, '#skF_7': $i).
% 3.14/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.14/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.14/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.52  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.14/1.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.14/1.52  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 3.14/1.52  tff('#skF_8', type, '#skF_8': $i).
% 3.14/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.52  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.14/1.52  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.14/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.14/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.52  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.14/1.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.14/1.52  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.14/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.14/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.14/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.52  
% 3.50/1.53  tff(f_140, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => r1_tarski(u1_struct_0(k4_waybel_9(A, B, C)), u1_struct_0(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_waybel_9)).
% 3.50/1.53  tff(f_123, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) & m1_subset_1(C, u1_struct_0(B))) => (v6_waybel_0(k4_waybel_9(A, B, C), A) & l1_waybel_0(k4_waybel_9(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_waybel_9)).
% 3.50/1.53  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.50/1.53  tff(f_107, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (![D]: ((v6_waybel_0(D, A) & l1_waybel_0(D, A)) => ((D = k4_waybel_9(A, B, C)) <=> (((![E]: (r2_hidden(E, u1_struct_0(D)) <=> (?[F]: ((m1_subset_1(F, u1_struct_0(B)) & (F = E)) & r1_orders_2(B, C, F))))) & r2_relset_1(u1_struct_0(D), u1_struct_0(D), u1_orders_2(D), k1_toler_1(u1_orders_2(B), u1_struct_0(D)))) & (u1_waybel_0(A, D) = k2_partfun1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), u1_struct_0(D))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_waybel_9)).
% 3.50/1.53  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.50/1.53  tff(f_55, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(u1_waybel_0(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 3.50/1.53  tff(f_45, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 3.50/1.53  tff(f_72, axiom, (![A, B]: ((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & ~v1_xboole_0(u1_waybel_0(A, B))) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc15_yellow_6)).
% 3.50/1.53  tff(c_66, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.50/1.53  tff(c_64, plain, (l1_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.50/1.53  tff(c_60, plain, (l1_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.50/1.53  tff(c_62, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.50/1.53  tff(c_58, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.50/1.53  tff(c_121, plain, (![A_232, B_233, C_234]: (l1_waybel_0(k4_waybel_9(A_232, B_233, C_234), A_232) | ~m1_subset_1(C_234, u1_struct_0(B_233)) | ~l1_waybel_0(B_233, A_232) | v2_struct_0(B_233) | ~l1_struct_0(A_232) | v2_struct_0(A_232))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.50/1.53  tff(c_123, plain, (![A_232]: (l1_waybel_0(k4_waybel_9(A_232, '#skF_7', '#skF_8'), A_232) | ~l1_waybel_0('#skF_7', A_232) | v2_struct_0('#skF_7') | ~l1_struct_0(A_232) | v2_struct_0(A_232))), inference(resolution, [status(thm)], [c_58, c_121])).
% 3.50/1.53  tff(c_126, plain, (![A_232]: (l1_waybel_0(k4_waybel_9(A_232, '#skF_7', '#skF_8'), A_232) | ~l1_waybel_0('#skF_7', A_232) | ~l1_struct_0(A_232) | v2_struct_0(A_232))), inference(negUnitSimplification, [status(thm)], [c_62, c_123])).
% 3.50/1.53  tff(c_54, plain, (![A_188, B_189, C_190]: (v6_waybel_0(k4_waybel_9(A_188, B_189, C_190), A_188) | ~m1_subset_1(C_190, u1_struct_0(B_189)) | ~l1_waybel_0(B_189, A_188) | v2_struct_0(B_189) | ~l1_struct_0(A_188) | v2_struct_0(A_188))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.50/1.53  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.50/1.53  tff(c_155, plain, (![C_254, A_255, B_256, E_257]: ('#skF_2'(C_254, A_255, B_256, E_257, k4_waybel_9(A_255, B_256, C_254))=E_257 | ~r2_hidden(E_257, u1_struct_0(k4_waybel_9(A_255, B_256, C_254))) | ~l1_waybel_0(k4_waybel_9(A_255, B_256, C_254), A_255) | ~v6_waybel_0(k4_waybel_9(A_255, B_256, C_254), A_255) | ~m1_subset_1(C_254, u1_struct_0(B_256)) | ~l1_waybel_0(B_256, A_255) | v2_struct_0(B_256) | ~l1_struct_0(A_255) | v2_struct_0(A_255))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.50/1.53  tff(c_281, plain, (![C_306, A_307, B_308, B_309]: ('#skF_2'(C_306, A_307, B_308, '#skF_1'(u1_struct_0(k4_waybel_9(A_307, B_308, C_306)), B_309), k4_waybel_9(A_307, B_308, C_306))='#skF_1'(u1_struct_0(k4_waybel_9(A_307, B_308, C_306)), B_309) | ~l1_waybel_0(k4_waybel_9(A_307, B_308, C_306), A_307) | ~v6_waybel_0(k4_waybel_9(A_307, B_308, C_306), A_307) | ~m1_subset_1(C_306, u1_struct_0(B_308)) | ~l1_waybel_0(B_308, A_307) | v2_struct_0(B_308) | ~l1_struct_0(A_307) | v2_struct_0(A_307) | r1_tarski(u1_struct_0(k4_waybel_9(A_307, B_308, C_306)), B_309))), inference(resolution, [status(thm)], [c_6, c_155])).
% 3.50/1.53  tff(c_50, plain, (![C_148, A_16, B_104, E_181]: (m1_subset_1('#skF_2'(C_148, A_16, B_104, E_181, k4_waybel_9(A_16, B_104, C_148)), u1_struct_0(B_104)) | ~r2_hidden(E_181, u1_struct_0(k4_waybel_9(A_16, B_104, C_148))) | ~l1_waybel_0(k4_waybel_9(A_16, B_104, C_148), A_16) | ~v6_waybel_0(k4_waybel_9(A_16, B_104, C_148), A_16) | ~m1_subset_1(C_148, u1_struct_0(B_104)) | ~l1_waybel_0(B_104, A_16) | v2_struct_0(B_104) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.50/1.53  tff(c_346, plain, (![A_346, B_347, C_348, B_349]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_346, B_347, C_348)), B_349), u1_struct_0(B_347)) | ~r2_hidden('#skF_1'(u1_struct_0(k4_waybel_9(A_346, B_347, C_348)), B_349), u1_struct_0(k4_waybel_9(A_346, B_347, C_348))) | ~l1_waybel_0(k4_waybel_9(A_346, B_347, C_348), A_346) | ~v6_waybel_0(k4_waybel_9(A_346, B_347, C_348), A_346) | ~m1_subset_1(C_348, u1_struct_0(B_347)) | ~l1_waybel_0(B_347, A_346) | v2_struct_0(B_347) | ~l1_struct_0(A_346) | v2_struct_0(A_346) | ~l1_waybel_0(k4_waybel_9(A_346, B_347, C_348), A_346) | ~v6_waybel_0(k4_waybel_9(A_346, B_347, C_348), A_346) | ~m1_subset_1(C_348, u1_struct_0(B_347)) | ~l1_waybel_0(B_347, A_346) | v2_struct_0(B_347) | ~l1_struct_0(A_346) | v2_struct_0(A_346) | r1_tarski(u1_struct_0(k4_waybel_9(A_346, B_347, C_348)), B_349))), inference(superposition, [status(thm), theory('equality')], [c_281, c_50])).
% 3.50/1.53  tff(c_388, plain, (![A_355, B_356, C_357, B_358]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_355, B_356, C_357)), B_358), u1_struct_0(B_356)) | ~l1_waybel_0(k4_waybel_9(A_355, B_356, C_357), A_355) | ~v6_waybel_0(k4_waybel_9(A_355, B_356, C_357), A_355) | ~m1_subset_1(C_357, u1_struct_0(B_356)) | ~l1_waybel_0(B_356, A_355) | v2_struct_0(B_356) | ~l1_struct_0(A_355) | v2_struct_0(A_355) | r1_tarski(u1_struct_0(k4_waybel_9(A_355, B_356, C_357)), B_358))), inference(resolution, [status(thm)], [c_6, c_346])).
% 3.50/1.53  tff(c_392, plain, (![A_359, B_360, C_361, B_362]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_359, B_360, C_361)), B_362), u1_struct_0(B_360)) | ~l1_waybel_0(k4_waybel_9(A_359, B_360, C_361), A_359) | r1_tarski(u1_struct_0(k4_waybel_9(A_359, B_360, C_361)), B_362) | ~m1_subset_1(C_361, u1_struct_0(B_360)) | ~l1_waybel_0(B_360, A_359) | v2_struct_0(B_360) | ~l1_struct_0(A_359) | v2_struct_0(A_359))), inference(resolution, [status(thm)], [c_54, c_388])).
% 3.50/1.53  tff(c_396, plain, (![A_232, B_362]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_232, '#skF_7', '#skF_8')), B_362), u1_struct_0('#skF_7')) | r1_tarski(u1_struct_0(k4_waybel_9(A_232, '#skF_7', '#skF_8')), B_362) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | v2_struct_0('#skF_7') | ~l1_waybel_0('#skF_7', A_232) | ~l1_struct_0(A_232) | v2_struct_0(A_232))), inference(resolution, [status(thm)], [c_126, c_392])).
% 3.50/1.53  tff(c_400, plain, (![A_232, B_362]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_232, '#skF_7', '#skF_8')), B_362), u1_struct_0('#skF_7')) | r1_tarski(u1_struct_0(k4_waybel_9(A_232, '#skF_7', '#skF_8')), B_362) | v2_struct_0('#skF_7') | ~l1_waybel_0('#skF_7', A_232) | ~l1_struct_0(A_232) | v2_struct_0(A_232))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_396])).
% 3.50/1.53  tff(c_402, plain, (![A_363, B_364]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_363, '#skF_7', '#skF_8')), B_364), u1_struct_0('#skF_7')) | r1_tarski(u1_struct_0(k4_waybel_9(A_363, '#skF_7', '#skF_8')), B_364) | ~l1_waybel_0('#skF_7', A_363) | ~l1_struct_0(A_363) | v2_struct_0(A_363))), inference(negUnitSimplification, [status(thm)], [c_62, c_400])).
% 3.50/1.53  tff(c_75, plain, (![A_200, B_201]: (r2_hidden(A_200, B_201) | v1_xboole_0(B_201) | ~m1_subset_1(A_200, B_201))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.50/1.53  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.50/1.53  tff(c_80, plain, (![A_1, B_201]: (r1_tarski(A_1, B_201) | v1_xboole_0(B_201) | ~m1_subset_1('#skF_1'(A_1, B_201), B_201))), inference(resolution, [status(thm)], [c_75, c_4])).
% 3.50/1.53  tff(c_420, plain, (![A_363]: (v1_xboole_0(u1_struct_0('#skF_7')) | r1_tarski(u1_struct_0(k4_waybel_9(A_363, '#skF_7', '#skF_8')), u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_7', A_363) | ~l1_struct_0(A_363) | v2_struct_0(A_363))), inference(resolution, [status(thm)], [c_402, c_80])).
% 3.50/1.53  tff(c_421, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_420])).
% 3.50/1.53  tff(c_110, plain, (![A_226, B_227]: (m1_subset_1(u1_waybel_0(A_226, B_227), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_227), u1_struct_0(A_226)))) | ~l1_waybel_0(B_227, A_226) | ~l1_struct_0(A_226))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.50/1.53  tff(c_10, plain, (![C_11, A_8, B_9]: (v1_xboole_0(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.50/1.53  tff(c_115, plain, (![A_228, B_229]: (v1_xboole_0(u1_waybel_0(A_228, B_229)) | ~v1_xboole_0(u1_struct_0(B_229)) | ~l1_waybel_0(B_229, A_228) | ~l1_struct_0(A_228))), inference(resolution, [status(thm)], [c_110, c_10])).
% 3.50/1.53  tff(c_20, plain, (![A_14, B_15]: (~v1_xboole_0(u1_waybel_0(A_14, B_15)) | ~l1_waybel_0(B_15, A_14) | v2_struct_0(B_15) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.50/1.53  tff(c_119, plain, (![B_229, A_228]: (v2_struct_0(B_229) | v2_struct_0(A_228) | ~v1_xboole_0(u1_struct_0(B_229)) | ~l1_waybel_0(B_229, A_228) | ~l1_struct_0(A_228))), inference(resolution, [status(thm)], [c_115, c_20])).
% 3.50/1.53  tff(c_423, plain, (![A_228]: (v2_struct_0('#skF_7') | v2_struct_0(A_228) | ~l1_waybel_0('#skF_7', A_228) | ~l1_struct_0(A_228))), inference(resolution, [status(thm)], [c_421, c_119])).
% 3.50/1.53  tff(c_431, plain, (![A_369]: (v2_struct_0(A_369) | ~l1_waybel_0('#skF_7', A_369) | ~l1_struct_0(A_369))), inference(negUnitSimplification, [status(thm)], [c_62, c_423])).
% 3.50/1.53  tff(c_434, plain, (v2_struct_0('#skF_6') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_60, c_431])).
% 3.50/1.53  tff(c_437, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_434])).
% 3.50/1.53  tff(c_439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_437])).
% 3.50/1.53  tff(c_442, plain, (![A_370]: (r1_tarski(u1_struct_0(k4_waybel_9(A_370, '#skF_7', '#skF_8')), u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_7', A_370) | ~l1_struct_0(A_370) | v2_struct_0(A_370))), inference(splitRight, [status(thm)], [c_420])).
% 3.50/1.53  tff(c_56, plain, (~r1_tarski(u1_struct_0(k4_waybel_9('#skF_6', '#skF_7', '#skF_8')), u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.50/1.53  tff(c_451, plain, (~l1_waybel_0('#skF_7', '#skF_6') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_442, c_56])).
% 3.50/1.53  tff(c_457, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_451])).
% 3.50/1.53  tff(c_459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_457])).
% 3.50/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.53  
% 3.50/1.53  Inference rules
% 3.50/1.53  ----------------------
% 3.50/1.53  #Ref     : 0
% 3.50/1.53  #Sup     : 78
% 3.50/1.53  #Fact    : 0
% 3.50/1.53  #Define  : 0
% 3.50/1.53  #Split   : 2
% 3.50/1.53  #Chain   : 0
% 3.50/1.53  #Close   : 0
% 3.50/1.53  
% 3.50/1.53  Ordering : KBO
% 3.50/1.53  
% 3.50/1.53  Simplification rules
% 3.50/1.53  ----------------------
% 3.50/1.53  #Subsume      : 22
% 3.50/1.53  #Demod        : 17
% 3.50/1.53  #Tautology    : 10
% 3.50/1.53  #SimpNegUnit  : 18
% 3.50/1.53  #BackRed      : 0
% 3.50/1.53  
% 3.50/1.53  #Partial instantiations: 0
% 3.50/1.53  #Strategies tried      : 1
% 3.50/1.53  
% 3.50/1.53  Timing (in seconds)
% 3.50/1.53  ----------------------
% 3.50/1.54  Preprocessing        : 0.37
% 3.50/1.54  Parsing              : 0.18
% 3.50/1.54  CNF conversion       : 0.04
% 3.50/1.54  Main loop            : 0.39
% 3.50/1.54  Inferencing          : 0.15
% 3.50/1.54  Reduction            : 0.10
% 3.50/1.54  Demodulation         : 0.06
% 3.50/1.54  BG Simplification    : 0.03
% 3.50/1.54  Subsumption          : 0.10
% 3.50/1.54  Abstraction          : 0.02
% 3.50/1.54  MUC search           : 0.00
% 3.50/1.54  Cooper               : 0.00
% 3.50/1.54  Total                : 0.80
% 3.50/1.54  Index Insertion      : 0.00
% 3.50/1.54  Index Deletion       : 0.00
% 3.50/1.54  Index Matching       : 0.00
% 3.50/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
