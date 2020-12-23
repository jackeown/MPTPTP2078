%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:08 EST 2020

% Result     : Theorem 4.64s
% Output     : CNFRefutation 4.64s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 115 expanded)
%              Number of leaves         :   32 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  198 ( 348 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > k4_waybel_9 > a_3_0_waybel_9 > u1_waybel_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k4_waybel_9,type,(
    k4_waybel_9: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(a_3_0_waybel_9,type,(
    a_3_0_waybel_9: ( $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(B)
        & l1_struct_0(B)
        & ~ v2_struct_0(C)
        & l1_waybel_0(C,B)
        & m1_subset_1(D,u1_struct_0(C)) )
     => ( r2_hidden(A,a_3_0_waybel_9(B,C,D))
      <=> ? [E] :
            ( m1_subset_1(E,u1_struct_0(C))
            & A = E
            & r1_orders_2(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => u1_struct_0(k4_waybel_9(A,B,C)) = a_3_0_waybel_9(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_waybel_9)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(u1_waybel_0(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & ~ v1_xboole_0(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc15_yellow_6)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_48,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_44,plain,(
    l1_waybel_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_51,plain,(
    ! [B_34,A_35] :
      ( v1_xboole_0(B_34)
      | ~ m1_subset_1(B_34,A_35)
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_55,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_51])).

tff(c_56,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_74,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),A_44)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_82,plain,(
    ! [A_44] : r1_tarski(A_44,A_44) ),
    inference(resolution,[status(thm)],[c_74,c_4])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,(
    ! [C_47,B_48,A_49] :
      ( r2_hidden(C_47,B_48)
      | ~ r2_hidden(C_47,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,(
    ! [A_1,B_2,B_48] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_48)
      | ~ r1_tarski(A_1,B_48)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_85])).

tff(c_236,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( '#skF_2'(A_95,B_96,C_97,D_98) = A_95
      | ~ r2_hidden(A_95,a_3_0_waybel_9(B_96,C_97,D_98))
      | ~ m1_subset_1(D_98,u1_struct_0(C_97))
      | ~ l1_waybel_0(C_97,B_96)
      | v2_struct_0(C_97)
      | ~ l1_struct_0(B_96)
      | v2_struct_0(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_483,plain,(
    ! [B_151,C_152,D_153,B_154] :
      ( '#skF_2'('#skF_1'(a_3_0_waybel_9(B_151,C_152,D_153),B_154),B_151,C_152,D_153) = '#skF_1'(a_3_0_waybel_9(B_151,C_152,D_153),B_154)
      | ~ m1_subset_1(D_153,u1_struct_0(C_152))
      | ~ l1_waybel_0(C_152,B_151)
      | v2_struct_0(C_152)
      | ~ l1_struct_0(B_151)
      | v2_struct_0(B_151)
      | r1_tarski(a_3_0_waybel_9(B_151,C_152,D_153),B_154) ) ),
    inference(resolution,[status(thm)],[c_6,c_236])).

tff(c_36,plain,(
    ! [A_16,B_17,C_18,D_19] :
      ( m1_subset_1('#skF_2'(A_16,B_17,C_18,D_19),u1_struct_0(C_18))
      | ~ r2_hidden(A_16,a_3_0_waybel_9(B_17,C_18,D_19))
      | ~ m1_subset_1(D_19,u1_struct_0(C_18))
      | ~ l1_waybel_0(C_18,B_17)
      | v2_struct_0(C_18)
      | ~ l1_struct_0(B_17)
      | v2_struct_0(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1430,plain,(
    ! [B_299,C_300,D_301,B_302] :
      ( m1_subset_1('#skF_1'(a_3_0_waybel_9(B_299,C_300,D_301),B_302),u1_struct_0(C_300))
      | ~ r2_hidden('#skF_1'(a_3_0_waybel_9(B_299,C_300,D_301),B_302),a_3_0_waybel_9(B_299,C_300,D_301))
      | ~ m1_subset_1(D_301,u1_struct_0(C_300))
      | ~ l1_waybel_0(C_300,B_299)
      | v2_struct_0(C_300)
      | ~ l1_struct_0(B_299)
      | v2_struct_0(B_299)
      | ~ m1_subset_1(D_301,u1_struct_0(C_300))
      | ~ l1_waybel_0(C_300,B_299)
      | v2_struct_0(C_300)
      | ~ l1_struct_0(B_299)
      | v2_struct_0(B_299)
      | r1_tarski(a_3_0_waybel_9(B_299,C_300,D_301),B_302) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_36])).

tff(c_1438,plain,(
    ! [B_299,C_300,D_301,B_2] :
      ( m1_subset_1('#skF_1'(a_3_0_waybel_9(B_299,C_300,D_301),B_2),u1_struct_0(C_300))
      | ~ m1_subset_1(D_301,u1_struct_0(C_300))
      | ~ l1_waybel_0(C_300,B_299)
      | v2_struct_0(C_300)
      | ~ l1_struct_0(B_299)
      | v2_struct_0(B_299)
      | ~ r1_tarski(a_3_0_waybel_9(B_299,C_300,D_301),a_3_0_waybel_9(B_299,C_300,D_301))
      | r1_tarski(a_3_0_waybel_9(B_299,C_300,D_301),B_2) ) ),
    inference(resolution,[status(thm)],[c_90,c_1430])).

tff(c_1452,plain,(
    ! [B_303,C_304,D_305,B_306] :
      ( m1_subset_1('#skF_1'(a_3_0_waybel_9(B_303,C_304,D_305),B_306),u1_struct_0(C_304))
      | ~ m1_subset_1(D_305,u1_struct_0(C_304))
      | ~ l1_waybel_0(C_304,B_303)
      | v2_struct_0(C_304)
      | ~ l1_struct_0(B_303)
      | v2_struct_0(B_303)
      | r1_tarski(a_3_0_waybel_9(B_303,C_304,D_305),B_306) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1438])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r2_hidden(B_7,A_6)
      | ~ m1_subset_1(B_7,A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_68,plain,(
    ! [A_42,B_43] :
      ( ~ r2_hidden('#skF_1'(A_42,B_43),B_43)
      | r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_73,plain,(
    ! [A_42,A_6] :
      ( r1_tarski(A_42,A_6)
      | ~ m1_subset_1('#skF_1'(A_42,A_6),A_6)
      | v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_68])).

tff(c_1498,plain,(
    ! [C_307,D_308,B_309] :
      ( v1_xboole_0(u1_struct_0(C_307))
      | ~ m1_subset_1(D_308,u1_struct_0(C_307))
      | ~ l1_waybel_0(C_307,B_309)
      | v2_struct_0(C_307)
      | ~ l1_struct_0(B_309)
      | v2_struct_0(B_309)
      | r1_tarski(a_3_0_waybel_9(B_309,C_307,D_308),u1_struct_0(C_307)) ) ),
    inference(resolution,[status(thm)],[c_1452,c_73])).

tff(c_174,plain,(
    ! [A_82,B_83,C_84] :
      ( u1_struct_0(k4_waybel_9(A_82,B_83,C_84)) = a_3_0_waybel_9(A_82,B_83,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(B_83))
      | ~ l1_waybel_0(B_83,A_82)
      | v2_struct_0(B_83)
      | ~ l1_struct_0(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_185,plain,(
    ! [A_82] :
      ( u1_struct_0(k4_waybel_9(A_82,'#skF_4','#skF_5')) = a_3_0_waybel_9(A_82,'#skF_4','#skF_5')
      | ~ l1_waybel_0('#skF_4',A_82)
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0(A_82)
      | v2_struct_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_42,c_174])).

tff(c_193,plain,(
    ! [A_87] :
      ( u1_struct_0(k4_waybel_9(A_87,'#skF_4','#skF_5')) = a_3_0_waybel_9(A_87,'#skF_4','#skF_5')
      | ~ l1_waybel_0('#skF_4',A_87)
      | ~ l1_struct_0(A_87)
      | v2_struct_0(A_87) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_185])).

tff(c_40,plain,(
    ~ r1_tarski(u1_struct_0(k4_waybel_9('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_221,plain,
    ( ~ r1_tarski(a_3_0_waybel_9('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_40])).

tff(c_227,plain,
    ( ~ r1_tarski(a_3_0_waybel_9('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_221])).

tff(c_228,plain,(
    ~ r1_tarski(a_3_0_waybel_9('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_227])).

tff(c_1503,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1498,c_228])).

tff(c_1526,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_42,c_1503])).

tff(c_1528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_46,c_56,c_1526])).

tff(c_1530,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_1633,plain,(
    ! [A_350,B_351] :
      ( m1_subset_1(u1_waybel_0(A_350,B_351),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_351),u1_struct_0(A_350))))
      | ~ l1_waybel_0(B_351,A_350)
      | ~ l1_struct_0(A_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    ! [C_11,A_8,B_9] :
      ( v1_xboole_0(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1660,plain,(
    ! [A_355,B_356] :
      ( v1_xboole_0(u1_waybel_0(A_355,B_356))
      | ~ v1_xboole_0(u1_struct_0(B_356))
      | ~ l1_waybel_0(B_356,A_355)
      | ~ l1_struct_0(A_355) ) ),
    inference(resolution,[status(thm)],[c_1633,c_16])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( ~ v1_xboole_0(u1_waybel_0(A_14,B_15))
      | ~ l1_waybel_0(B_15,A_14)
      | v2_struct_0(B_15)
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1665,plain,(
    ! [B_357,A_358] :
      ( v2_struct_0(B_357)
      | v2_struct_0(A_358)
      | ~ v1_xboole_0(u1_struct_0(B_357))
      | ~ l1_waybel_0(B_357,A_358)
      | ~ l1_struct_0(A_358) ) ),
    inference(resolution,[status(thm)],[c_1660,c_26])).

tff(c_1667,plain,(
    ! [A_358] :
      ( v2_struct_0('#skF_4')
      | v2_struct_0(A_358)
      | ~ l1_waybel_0('#skF_4',A_358)
      | ~ l1_struct_0(A_358) ) ),
    inference(resolution,[status(thm)],[c_1530,c_1665])).

tff(c_1671,plain,(
    ! [A_359] :
      ( v2_struct_0(A_359)
      | ~ l1_waybel_0('#skF_4',A_359)
      | ~ l1_struct_0(A_359) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1667])).

tff(c_1674,plain,
    ( v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1671])).

tff(c_1677,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1674])).

tff(c_1679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1677])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n003.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 12:23:12 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.64/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.73  
% 4.64/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.73  %$ v1_funct_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > k4_waybel_9 > a_3_0_waybel_9 > u1_waybel_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.64/1.73  
% 4.64/1.73  %Foreground sorts:
% 4.64/1.73  
% 4.64/1.73  
% 4.64/1.73  %Background operators:
% 4.64/1.73  
% 4.64/1.73  
% 4.64/1.73  %Foreground operators:
% 4.64/1.73  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.64/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.64/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.64/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.64/1.73  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.64/1.73  tff(k4_waybel_9, type, k4_waybel_9: ($i * $i * $i) > $i).
% 4.64/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.64/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.64/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.64/1.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.64/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.64/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.64/1.73  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.64/1.73  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 4.64/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.64/1.73  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 4.64/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.64/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.64/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.64/1.73  tff(a_3_0_waybel_9, type, a_3_0_waybel_9: ($i * $i * $i) > $i).
% 4.64/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.64/1.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.64/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.64/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.64/1.73  
% 4.64/1.75  tff(f_133, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => r1_tarski(u1_struct_0(k4_waybel_9(A, B, C)), u1_struct_0(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_waybel_9)).
% 4.64/1.75  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.64/1.75  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.64/1.75  tff(f_100, axiom, (![A, B, C, D]: (((((~v2_struct_0(B) & l1_struct_0(B)) & ~v2_struct_0(C)) & l1_waybel_0(C, B)) & m1_subset_1(D, u1_struct_0(C))) => (r2_hidden(A, a_3_0_waybel_9(B, C, D)) <=> (?[E]: ((m1_subset_1(E, u1_struct_0(C)) & (A = E)) & r1_orders_2(C, D, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_3_0_waybel_9)).
% 4.64/1.75  tff(f_116, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (u1_struct_0(k4_waybel_9(A, B, C)) = a_3_0_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_waybel_9)).
% 4.64/1.75  tff(f_62, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(u1_waybel_0(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 4.64/1.75  tff(f_52, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 4.64/1.75  tff(f_79, axiom, (![A, B]: ((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & ~v1_xboole_0(u1_waybel_0(A, B))) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc15_yellow_6)).
% 4.64/1.75  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.64/1.75  tff(c_48, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.64/1.75  tff(c_44, plain, (l1_waybel_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.64/1.75  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.64/1.75  tff(c_42, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.64/1.75  tff(c_51, plain, (![B_34, A_35]: (v1_xboole_0(B_34) | ~m1_subset_1(B_34, A_35) | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.64/1.75  tff(c_55, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_51])).
% 4.64/1.75  tff(c_56, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_55])).
% 4.64/1.75  tff(c_74, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44, B_45), A_44) | r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.64/1.75  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.64/1.75  tff(c_82, plain, (![A_44]: (r1_tarski(A_44, A_44))), inference(resolution, [status(thm)], [c_74, c_4])).
% 4.64/1.75  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.64/1.75  tff(c_85, plain, (![C_47, B_48, A_49]: (r2_hidden(C_47, B_48) | ~r2_hidden(C_47, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.64/1.75  tff(c_90, plain, (![A_1, B_2, B_48]: (r2_hidden('#skF_1'(A_1, B_2), B_48) | ~r1_tarski(A_1, B_48) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_85])).
% 4.64/1.75  tff(c_236, plain, (![A_95, B_96, C_97, D_98]: ('#skF_2'(A_95, B_96, C_97, D_98)=A_95 | ~r2_hidden(A_95, a_3_0_waybel_9(B_96, C_97, D_98)) | ~m1_subset_1(D_98, u1_struct_0(C_97)) | ~l1_waybel_0(C_97, B_96) | v2_struct_0(C_97) | ~l1_struct_0(B_96) | v2_struct_0(B_96))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.64/1.75  tff(c_483, plain, (![B_151, C_152, D_153, B_154]: ('#skF_2'('#skF_1'(a_3_0_waybel_9(B_151, C_152, D_153), B_154), B_151, C_152, D_153)='#skF_1'(a_3_0_waybel_9(B_151, C_152, D_153), B_154) | ~m1_subset_1(D_153, u1_struct_0(C_152)) | ~l1_waybel_0(C_152, B_151) | v2_struct_0(C_152) | ~l1_struct_0(B_151) | v2_struct_0(B_151) | r1_tarski(a_3_0_waybel_9(B_151, C_152, D_153), B_154))), inference(resolution, [status(thm)], [c_6, c_236])).
% 4.64/1.75  tff(c_36, plain, (![A_16, B_17, C_18, D_19]: (m1_subset_1('#skF_2'(A_16, B_17, C_18, D_19), u1_struct_0(C_18)) | ~r2_hidden(A_16, a_3_0_waybel_9(B_17, C_18, D_19)) | ~m1_subset_1(D_19, u1_struct_0(C_18)) | ~l1_waybel_0(C_18, B_17) | v2_struct_0(C_18) | ~l1_struct_0(B_17) | v2_struct_0(B_17))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.64/1.75  tff(c_1430, plain, (![B_299, C_300, D_301, B_302]: (m1_subset_1('#skF_1'(a_3_0_waybel_9(B_299, C_300, D_301), B_302), u1_struct_0(C_300)) | ~r2_hidden('#skF_1'(a_3_0_waybel_9(B_299, C_300, D_301), B_302), a_3_0_waybel_9(B_299, C_300, D_301)) | ~m1_subset_1(D_301, u1_struct_0(C_300)) | ~l1_waybel_0(C_300, B_299) | v2_struct_0(C_300) | ~l1_struct_0(B_299) | v2_struct_0(B_299) | ~m1_subset_1(D_301, u1_struct_0(C_300)) | ~l1_waybel_0(C_300, B_299) | v2_struct_0(C_300) | ~l1_struct_0(B_299) | v2_struct_0(B_299) | r1_tarski(a_3_0_waybel_9(B_299, C_300, D_301), B_302))), inference(superposition, [status(thm), theory('equality')], [c_483, c_36])).
% 4.64/1.75  tff(c_1438, plain, (![B_299, C_300, D_301, B_2]: (m1_subset_1('#skF_1'(a_3_0_waybel_9(B_299, C_300, D_301), B_2), u1_struct_0(C_300)) | ~m1_subset_1(D_301, u1_struct_0(C_300)) | ~l1_waybel_0(C_300, B_299) | v2_struct_0(C_300) | ~l1_struct_0(B_299) | v2_struct_0(B_299) | ~r1_tarski(a_3_0_waybel_9(B_299, C_300, D_301), a_3_0_waybel_9(B_299, C_300, D_301)) | r1_tarski(a_3_0_waybel_9(B_299, C_300, D_301), B_2))), inference(resolution, [status(thm)], [c_90, c_1430])).
% 4.64/1.75  tff(c_1452, plain, (![B_303, C_304, D_305, B_306]: (m1_subset_1('#skF_1'(a_3_0_waybel_9(B_303, C_304, D_305), B_306), u1_struct_0(C_304)) | ~m1_subset_1(D_305, u1_struct_0(C_304)) | ~l1_waybel_0(C_304, B_303) | v2_struct_0(C_304) | ~l1_struct_0(B_303) | v2_struct_0(B_303) | r1_tarski(a_3_0_waybel_9(B_303, C_304, D_305), B_306))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1438])).
% 4.64/1.75  tff(c_10, plain, (![B_7, A_6]: (r2_hidden(B_7, A_6) | ~m1_subset_1(B_7, A_6) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.64/1.75  tff(c_68, plain, (![A_42, B_43]: (~r2_hidden('#skF_1'(A_42, B_43), B_43) | r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.64/1.75  tff(c_73, plain, (![A_42, A_6]: (r1_tarski(A_42, A_6) | ~m1_subset_1('#skF_1'(A_42, A_6), A_6) | v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_10, c_68])).
% 4.64/1.75  tff(c_1498, plain, (![C_307, D_308, B_309]: (v1_xboole_0(u1_struct_0(C_307)) | ~m1_subset_1(D_308, u1_struct_0(C_307)) | ~l1_waybel_0(C_307, B_309) | v2_struct_0(C_307) | ~l1_struct_0(B_309) | v2_struct_0(B_309) | r1_tarski(a_3_0_waybel_9(B_309, C_307, D_308), u1_struct_0(C_307)))), inference(resolution, [status(thm)], [c_1452, c_73])).
% 4.64/1.75  tff(c_174, plain, (![A_82, B_83, C_84]: (u1_struct_0(k4_waybel_9(A_82, B_83, C_84))=a_3_0_waybel_9(A_82, B_83, C_84) | ~m1_subset_1(C_84, u1_struct_0(B_83)) | ~l1_waybel_0(B_83, A_82) | v2_struct_0(B_83) | ~l1_struct_0(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.64/1.75  tff(c_185, plain, (![A_82]: (u1_struct_0(k4_waybel_9(A_82, '#skF_4', '#skF_5'))=a_3_0_waybel_9(A_82, '#skF_4', '#skF_5') | ~l1_waybel_0('#skF_4', A_82) | v2_struct_0('#skF_4') | ~l1_struct_0(A_82) | v2_struct_0(A_82))), inference(resolution, [status(thm)], [c_42, c_174])).
% 4.64/1.75  tff(c_193, plain, (![A_87]: (u1_struct_0(k4_waybel_9(A_87, '#skF_4', '#skF_5'))=a_3_0_waybel_9(A_87, '#skF_4', '#skF_5') | ~l1_waybel_0('#skF_4', A_87) | ~l1_struct_0(A_87) | v2_struct_0(A_87))), inference(negUnitSimplification, [status(thm)], [c_46, c_185])).
% 4.64/1.75  tff(c_40, plain, (~r1_tarski(u1_struct_0(k4_waybel_9('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.64/1.75  tff(c_221, plain, (~r1_tarski(a_3_0_waybel_9('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4')) | ~l1_waybel_0('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_193, c_40])).
% 4.64/1.75  tff(c_227, plain, (~r1_tarski(a_3_0_waybel_9('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_221])).
% 4.64/1.75  tff(c_228, plain, (~r1_tarski(a_3_0_waybel_9('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_50, c_227])).
% 4.64/1.75  tff(c_1503, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_waybel_0('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1498, c_228])).
% 4.64/1.75  tff(c_1526, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_42, c_1503])).
% 4.64/1.75  tff(c_1528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_46, c_56, c_1526])).
% 4.64/1.75  tff(c_1530, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_55])).
% 4.64/1.75  tff(c_1633, plain, (![A_350, B_351]: (m1_subset_1(u1_waybel_0(A_350, B_351), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_351), u1_struct_0(A_350)))) | ~l1_waybel_0(B_351, A_350) | ~l1_struct_0(A_350))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.64/1.75  tff(c_16, plain, (![C_11, A_8, B_9]: (v1_xboole_0(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.64/1.75  tff(c_1660, plain, (![A_355, B_356]: (v1_xboole_0(u1_waybel_0(A_355, B_356)) | ~v1_xboole_0(u1_struct_0(B_356)) | ~l1_waybel_0(B_356, A_355) | ~l1_struct_0(A_355))), inference(resolution, [status(thm)], [c_1633, c_16])).
% 4.64/1.75  tff(c_26, plain, (![A_14, B_15]: (~v1_xboole_0(u1_waybel_0(A_14, B_15)) | ~l1_waybel_0(B_15, A_14) | v2_struct_0(B_15) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.64/1.75  tff(c_1665, plain, (![B_357, A_358]: (v2_struct_0(B_357) | v2_struct_0(A_358) | ~v1_xboole_0(u1_struct_0(B_357)) | ~l1_waybel_0(B_357, A_358) | ~l1_struct_0(A_358))), inference(resolution, [status(thm)], [c_1660, c_26])).
% 4.64/1.75  tff(c_1667, plain, (![A_358]: (v2_struct_0('#skF_4') | v2_struct_0(A_358) | ~l1_waybel_0('#skF_4', A_358) | ~l1_struct_0(A_358))), inference(resolution, [status(thm)], [c_1530, c_1665])).
% 4.64/1.75  tff(c_1671, plain, (![A_359]: (v2_struct_0(A_359) | ~l1_waybel_0('#skF_4', A_359) | ~l1_struct_0(A_359))), inference(negUnitSimplification, [status(thm)], [c_46, c_1667])).
% 4.64/1.75  tff(c_1674, plain, (v2_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_1671])).
% 4.64/1.75  tff(c_1677, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1674])).
% 4.64/1.75  tff(c_1679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1677])).
% 4.64/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.75  
% 4.64/1.75  Inference rules
% 4.64/1.75  ----------------------
% 4.64/1.75  #Ref     : 0
% 4.64/1.75  #Sup     : 403
% 4.64/1.75  #Fact    : 0
% 4.64/1.75  #Define  : 0
% 4.64/1.75  #Split   : 3
% 4.64/1.75  #Chain   : 0
% 4.64/1.75  #Close   : 0
% 4.64/1.75  
% 4.64/1.75  Ordering : KBO
% 4.64/1.75  
% 4.64/1.75  Simplification rules
% 4.64/1.75  ----------------------
% 4.64/1.75  #Subsume      : 76
% 4.64/1.75  #Demod        : 32
% 4.64/1.75  #Tautology    : 54
% 4.64/1.75  #SimpNegUnit  : 38
% 4.64/1.75  #BackRed      : 0
% 4.64/1.75  
% 4.64/1.75  #Partial instantiations: 0
% 4.64/1.75  #Strategies tried      : 1
% 4.64/1.75  
% 4.64/1.75  Timing (in seconds)
% 4.64/1.75  ----------------------
% 4.64/1.75  Preprocessing        : 0.31
% 4.64/1.75  Parsing              : 0.18
% 4.64/1.75  CNF conversion       : 0.02
% 4.64/1.75  Main loop            : 0.82
% 4.64/1.75  Inferencing          : 0.30
% 4.64/1.75  Reduction            : 0.19
% 4.64/1.75  Demodulation         : 0.13
% 4.64/1.75  BG Simplification    : 0.04
% 4.64/1.75  Subsumption          : 0.23
% 4.64/1.75  Abstraction          : 0.04
% 4.64/1.75  MUC search           : 0.00
% 4.64/1.75  Cooper               : 0.00
% 4.64/1.75  Total                : 1.17
% 4.64/1.75  Index Insertion      : 0.00
% 4.64/1.75  Index Deletion       : 0.00
% 4.64/1.75  Index Matching       : 0.00
% 4.64/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
