%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1644+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:11 EST 2020

% Result     : Theorem 5.80s
% Output     : CNFRefutation 6.18s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 264 expanded)
%              Number of leaves         :   26 (  99 expanded)
%              Depth                    :   15
%              Number of atoms          :  252 ( 844 expanded)
%              Number of equality atoms :    1 (   7 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_orders_2 > k4_waybel_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_6 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k4_waybel_0,type,(
    k4_waybel_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v13_waybel_0(B,A)
            <=> r1_tarski(k4_waybel_0(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_waybel_0)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v13_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r1_orders_2(A,C,D) )
                     => r2_hidden(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k4_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_0)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = k4_waybel_0(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_hidden(D,C)
                    <=> ? [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                          & r1_orders_2(A,E,D)
                          & r2_hidden(E,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_waybel_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_54,plain,
    ( ~ r1_tarski(k4_waybel_0('#skF_7','#skF_8'),'#skF_8')
    | ~ v13_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_61,plain,(
    ~ v13_waybel_0('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,
    ( v13_waybel_0('#skF_8','#skF_7')
    | r1_tarski(k4_waybel_0('#skF_7','#skF_8'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_63,plain,(
    r1_tarski(k4_waybel_0('#skF_7','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_60])).

tff(c_52,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_50,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    ! [A_85,B_99] :
      ( m1_subset_1('#skF_5'(A_85,B_99),u1_struct_0(A_85))
      | v13_waybel_0(B_99,A_85)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_orders_2(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_38,plain,(
    ! [A_85,B_99] :
      ( m1_subset_1('#skF_4'(A_85,B_99),u1_struct_0(A_85))
      | v13_waybel_0(B_99,A_85)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_orders_2(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_46,plain,(
    ! [A_115,B_116] :
      ( m1_subset_1(k4_waybel_0(A_115,B_116),k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_orders_2(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [A_85,B_99] :
      ( r1_orders_2(A_85,'#skF_4'(A_85,B_99),'#skF_5'(A_85,B_99))
      | v13_waybel_0(B_99,A_85)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_orders_2(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_109,plain,(
    ! [A_144,B_145] :
      ( r2_hidden('#skF_4'(A_144,B_145),B_145)
      | v13_waybel_0(B_145,A_144)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_orders_2(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_113,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_8')
    | v13_waybel_0('#skF_8','#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_109])).

tff(c_117,plain,
    ( r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_8')
    | v13_waybel_0('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_113])).

tff(c_118,plain,(
    r2_hidden('#skF_4'('#skF_7','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_117])).

tff(c_422,plain,(
    ! [D_281,A_282,B_283,E_284] :
      ( r2_hidden(D_281,k4_waybel_0(A_282,B_283))
      | ~ r2_hidden(E_284,B_283)
      | ~ r1_orders_2(A_282,E_284,D_281)
      | ~ m1_subset_1(E_284,u1_struct_0(A_282))
      | ~ m1_subset_1(D_281,u1_struct_0(A_282))
      | ~ m1_subset_1(k4_waybel_0(A_282,B_283),k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ m1_subset_1(B_283,k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ l1_orders_2(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_507,plain,(
    ! [D_301,A_302] :
      ( r2_hidden(D_301,k4_waybel_0(A_302,'#skF_8'))
      | ~ r1_orders_2(A_302,'#skF_4'('#skF_7','#skF_8'),D_301)
      | ~ m1_subset_1('#skF_4'('#skF_7','#skF_8'),u1_struct_0(A_302))
      | ~ m1_subset_1(D_301,u1_struct_0(A_302))
      | ~ m1_subset_1(k4_waybel_0(A_302,'#skF_8'),k1_zfmisc_1(u1_struct_0(A_302)))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0(A_302)))
      | ~ l1_orders_2(A_302) ) ),
    inference(resolution,[status(thm)],[c_118,c_422])).

tff(c_510,plain,
    ( r2_hidden('#skF_5'('#skF_7','#skF_8'),k4_waybel_0('#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_4'('#skF_7','#skF_8'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_5'('#skF_7','#skF_8'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1(k4_waybel_0('#skF_7','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7')))
    | v13_waybel_0('#skF_8','#skF_7')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_507])).

tff(c_513,plain,
    ( r2_hidden('#skF_5'('#skF_7','#skF_8'),k4_waybel_0('#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_4'('#skF_7','#skF_8'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_5'('#skF_7','#skF_8'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1(k4_waybel_0('#skF_7','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7')))
    | v13_waybel_0('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_510])).

tff(c_514,plain,
    ( r2_hidden('#skF_5'('#skF_7','#skF_8'),k4_waybel_0('#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_4'('#skF_7','#skF_8'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_5'('#skF_7','#skF_8'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1(k4_waybel_0('#skF_7','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_513])).

tff(c_515,plain,(
    ~ m1_subset_1(k4_waybel_0('#skF_7','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_514])).

tff(c_518,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_515])).

tff(c_522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_518])).

tff(c_523,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_7','#skF_8'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_4'('#skF_7','#skF_8'),u1_struct_0('#skF_7'))
    | r2_hidden('#skF_5'('#skF_7','#skF_8'),k4_waybel_0('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_514])).

tff(c_652,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_523])).

tff(c_655,plain,
    ( v13_waybel_0('#skF_8','#skF_7')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_652])).

tff(c_661,plain,(
    v13_waybel_0('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_655])).

tff(c_663,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_661])).

tff(c_664,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_7','#skF_8'),u1_struct_0('#skF_7'))
    | r2_hidden('#skF_5'('#skF_7','#skF_8'),k4_waybel_0('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_523])).

tff(c_666,plain,(
    ~ m1_subset_1('#skF_5'('#skF_7','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_664])).

tff(c_677,plain,
    ( v13_waybel_0('#skF_8','#skF_7')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_666])).

tff(c_683,plain,(
    v13_waybel_0('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_677])).

tff(c_685,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_683])).

tff(c_686,plain,(
    r2_hidden('#skF_5'('#skF_7','#skF_8'),k4_waybel_0('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_664])).

tff(c_40,plain,(
    ! [C_114,B_111,A_110] :
      ( r2_hidden(C_114,B_111)
      | ~ r2_hidden(C_114,A_110)
      | ~ r1_tarski(A_110,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_711,plain,(
    ! [B_313] :
      ( r2_hidden('#skF_5'('#skF_7','#skF_8'),B_313)
      | ~ r1_tarski(k4_waybel_0('#skF_7','#skF_8'),B_313) ) ),
    inference(resolution,[status(thm)],[c_686,c_40])).

tff(c_30,plain,(
    ! [A_85,B_99] :
      ( ~ r2_hidden('#skF_5'(A_85,B_99),B_99)
      | v13_waybel_0(B_99,A_85)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_orders_2(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_723,plain,
    ( v13_waybel_0('#skF_8','#skF_7')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_orders_2('#skF_7')
    | ~ r1_tarski(k4_waybel_0('#skF_7','#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_711,c_30])).

tff(c_733,plain,(
    v13_waybel_0('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_52,c_50,c_723])).

tff(c_735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_733])).

tff(c_736,plain,(
    ~ r1_tarski(k4_waybel_0('#skF_7','#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_739,plain,(
    ! [A_316,B_317] :
      ( r2_hidden('#skF_6'(A_316,B_317),A_316)
      | r1_tarski(A_316,B_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,(
    ! [A_110,B_111] :
      ( ~ r2_hidden('#skF_6'(A_110,B_111),B_111)
      | r1_tarski(A_110,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_744,plain,(
    ! [A_316] : r1_tarski(A_316,A_316) ),
    inference(resolution,[status(thm)],[c_739,c_42])).

tff(c_44,plain,(
    ! [A_110,B_111] :
      ( r2_hidden('#skF_6'(A_110,B_111),A_110)
      | r1_tarski(A_110,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_748,plain,(
    ! [C_319,B_320,A_321] :
      ( r2_hidden(C_319,B_320)
      | ~ r2_hidden(C_319,A_321)
      | ~ r1_tarski(A_321,B_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_751,plain,(
    ! [A_110,B_111,B_320] :
      ( r2_hidden('#skF_6'(A_110,B_111),B_320)
      | ~ r1_tarski(A_110,B_320)
      | r1_tarski(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_44,c_748])).

tff(c_766,plain,(
    ! [A_329,B_330] :
      ( m1_subset_1(k4_waybel_0(A_329,B_330),k1_zfmisc_1(u1_struct_0(A_329)))
      | ~ m1_subset_1(B_330,k1_zfmisc_1(u1_struct_0(A_329)))
      | ~ l1_orders_2(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_48,plain,(
    ! [A_117,C_119,B_118] :
      ( m1_subset_1(A_117,C_119)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(C_119))
      | ~ r2_hidden(A_117,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_787,plain,(
    ! [A_345,A_346,B_347] :
      ( m1_subset_1(A_345,u1_struct_0(A_346))
      | ~ r2_hidden(A_345,k4_waybel_0(A_346,B_347))
      | ~ m1_subset_1(B_347,k1_zfmisc_1(u1_struct_0(A_346)))
      | ~ l1_orders_2(A_346) ) ),
    inference(resolution,[status(thm)],[c_766,c_48])).

tff(c_805,plain,(
    ! [A_355,B_356,A_357,B_358] :
      ( m1_subset_1('#skF_6'(A_355,B_356),u1_struct_0(A_357))
      | ~ m1_subset_1(B_358,k1_zfmisc_1(u1_struct_0(A_357)))
      | ~ l1_orders_2(A_357)
      | ~ r1_tarski(A_355,k4_waybel_0(A_357,B_358))
      | r1_tarski(A_355,B_356) ) ),
    inference(resolution,[status(thm)],[c_751,c_787])).

tff(c_809,plain,(
    ! [A_355,B_356] :
      ( m1_subset_1('#skF_6'(A_355,B_356),u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ r1_tarski(A_355,k4_waybel_0('#skF_7','#skF_8'))
      | r1_tarski(A_355,B_356) ) ),
    inference(resolution,[status(thm)],[c_50,c_805])).

tff(c_813,plain,(
    ! [A_355,B_356] :
      ( m1_subset_1('#skF_6'(A_355,B_356),u1_struct_0('#skF_7'))
      | ~ r1_tarski(A_355,k4_waybel_0('#skF_7','#skF_8'))
      | r1_tarski(A_355,B_356) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_809])).

tff(c_737,plain,(
    v13_waybel_0('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_925,plain,(
    ! [A_403,B_404,D_405] :
      ( r2_hidden('#skF_1'(A_403,B_404,k4_waybel_0(A_403,B_404),D_405),B_404)
      | ~ r2_hidden(D_405,k4_waybel_0(A_403,B_404))
      | ~ m1_subset_1(D_405,u1_struct_0(A_403))
      | ~ m1_subset_1(k4_waybel_0(A_403,B_404),k1_zfmisc_1(u1_struct_0(A_403)))
      | ~ m1_subset_1(B_404,k1_zfmisc_1(u1_struct_0(A_403)))
      | ~ l1_orders_2(A_403) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_928,plain,(
    ! [A_115,B_116,D_405] :
      ( r2_hidden('#skF_1'(A_115,B_116,k4_waybel_0(A_115,B_116),D_405),B_116)
      | ~ r2_hidden(D_405,k4_waybel_0(A_115,B_116))
      | ~ m1_subset_1(D_405,u1_struct_0(A_115))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_orders_2(A_115) ) ),
    inference(resolution,[status(thm)],[c_46,c_925])).

tff(c_752,plain,(
    ! [A_322,C_323,B_324] :
      ( m1_subset_1(A_322,C_323)
      | ~ m1_subset_1(B_324,k1_zfmisc_1(C_323))
      | ~ r2_hidden(A_322,B_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_755,plain,(
    ! [A_322] :
      ( m1_subset_1(A_322,u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_322,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_50,c_752])).

tff(c_958,plain,(
    ! [A_425,B_426,D_427] :
      ( r1_orders_2(A_425,'#skF_1'(A_425,B_426,k4_waybel_0(A_425,B_426),D_427),D_427)
      | ~ r2_hidden(D_427,k4_waybel_0(A_425,B_426))
      | ~ m1_subset_1(D_427,u1_struct_0(A_425))
      | ~ m1_subset_1(k4_waybel_0(A_425,B_426),k1_zfmisc_1(u1_struct_0(A_425)))
      | ~ m1_subset_1(B_426,k1_zfmisc_1(u1_struct_0(A_425)))
      | ~ l1_orders_2(A_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_962,plain,(
    ! [A_428,B_429,D_430] :
      ( r1_orders_2(A_428,'#skF_1'(A_428,B_429,k4_waybel_0(A_428,B_429),D_430),D_430)
      | ~ r2_hidden(D_430,k4_waybel_0(A_428,B_429))
      | ~ m1_subset_1(D_430,u1_struct_0(A_428))
      | ~ m1_subset_1(B_429,k1_zfmisc_1(u1_struct_0(A_428)))
      | ~ l1_orders_2(A_428) ) ),
    inference(resolution,[status(thm)],[c_46,c_958])).

tff(c_28,plain,(
    ! [D_108,B_99,A_85,C_106] :
      ( r2_hidden(D_108,B_99)
      | ~ r1_orders_2(A_85,C_106,D_108)
      | ~ r2_hidden(C_106,B_99)
      | ~ m1_subset_1(D_108,u1_struct_0(A_85))
      | ~ m1_subset_1(C_106,u1_struct_0(A_85))
      | ~ v13_waybel_0(B_99,A_85)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_orders_2(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1595,plain,(
    ! [D_651,B_652,A_653,B_654] :
      ( r2_hidden(D_651,B_652)
      | ~ r2_hidden('#skF_1'(A_653,B_654,k4_waybel_0(A_653,B_654),D_651),B_652)
      | ~ m1_subset_1('#skF_1'(A_653,B_654,k4_waybel_0(A_653,B_654),D_651),u1_struct_0(A_653))
      | ~ v13_waybel_0(B_652,A_653)
      | ~ m1_subset_1(B_652,k1_zfmisc_1(u1_struct_0(A_653)))
      | ~ r2_hidden(D_651,k4_waybel_0(A_653,B_654))
      | ~ m1_subset_1(D_651,u1_struct_0(A_653))
      | ~ m1_subset_1(B_654,k1_zfmisc_1(u1_struct_0(A_653)))
      | ~ l1_orders_2(A_653) ) ),
    inference(resolution,[status(thm)],[c_962,c_28])).

tff(c_1602,plain,(
    ! [D_655,B_656,A_657] :
      ( r2_hidden(D_655,B_656)
      | ~ m1_subset_1('#skF_1'(A_657,B_656,k4_waybel_0(A_657,B_656),D_655),u1_struct_0(A_657))
      | ~ v13_waybel_0(B_656,A_657)
      | ~ r2_hidden(D_655,k4_waybel_0(A_657,B_656))
      | ~ m1_subset_1(D_655,u1_struct_0(A_657))
      | ~ m1_subset_1(B_656,k1_zfmisc_1(u1_struct_0(A_657)))
      | ~ l1_orders_2(A_657) ) ),
    inference(resolution,[status(thm)],[c_928,c_1595])).

tff(c_1617,plain,(
    ! [D_655,B_656] :
      ( r2_hidden(D_655,B_656)
      | ~ v13_waybel_0(B_656,'#skF_7')
      | ~ r2_hidden(D_655,k4_waybel_0('#skF_7',B_656))
      | ~ m1_subset_1(D_655,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_656,k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ l1_orders_2('#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_7',B_656,k4_waybel_0('#skF_7',B_656),D_655),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_755,c_1602])).

tff(c_1864,plain,(
    ! [D_663,B_664] :
      ( r2_hidden(D_663,B_664)
      | ~ v13_waybel_0(B_664,'#skF_7')
      | ~ r2_hidden(D_663,k4_waybel_0('#skF_7',B_664))
      | ~ m1_subset_1(D_663,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_664,k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ r2_hidden('#skF_1'('#skF_7',B_664,k4_waybel_0('#skF_7',B_664),D_663),'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1617])).

tff(c_1872,plain,(
    ! [D_405] :
      ( r2_hidden(D_405,'#skF_8')
      | ~ v13_waybel_0('#skF_8','#skF_7')
      | ~ r2_hidden(D_405,k4_waybel_0('#skF_7','#skF_8'))
      | ~ m1_subset_1(D_405,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_928,c_1864])).

tff(c_1879,plain,(
    ! [D_665] :
      ( r2_hidden(D_665,'#skF_8')
      | ~ r2_hidden(D_665,k4_waybel_0('#skF_7','#skF_8'))
      | ~ m1_subset_1(D_665,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_737,c_1872])).

tff(c_2036,plain,(
    ! [A_666,B_667] :
      ( r2_hidden('#skF_6'(A_666,B_667),'#skF_8')
      | ~ m1_subset_1('#skF_6'(A_666,B_667),u1_struct_0('#skF_7'))
      | ~ r1_tarski(A_666,k4_waybel_0('#skF_7','#skF_8'))
      | r1_tarski(A_666,B_667) ) ),
    inference(resolution,[status(thm)],[c_751,c_1879])).

tff(c_2059,plain,(
    ! [A_668,B_669] :
      ( r2_hidden('#skF_6'(A_668,B_669),'#skF_8')
      | ~ r1_tarski(A_668,k4_waybel_0('#skF_7','#skF_8'))
      | r1_tarski(A_668,B_669) ) ),
    inference(resolution,[status(thm)],[c_813,c_2036])).

tff(c_2071,plain,(
    ! [A_670] :
      ( ~ r1_tarski(A_670,k4_waybel_0('#skF_7','#skF_8'))
      | r1_tarski(A_670,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2059,c_42])).

tff(c_2075,plain,(
    r1_tarski(k4_waybel_0('#skF_7','#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_744,c_2071])).

tff(c_2079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_736,c_2075])).

%------------------------------------------------------------------------------
