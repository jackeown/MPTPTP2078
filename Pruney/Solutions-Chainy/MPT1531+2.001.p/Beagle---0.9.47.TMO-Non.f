%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:58 EST 2020

% Result     : Timeout 59.70s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  300 (1226 expanded)
%              Number of leaves         :   37 ( 410 expanded)
%              Depth                    :   17
%              Number of atoms          :  798 (3668 expanded)
%              Number of equality atoms :   23 (  60 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B,C] :
            ( r1_tarski(B,C)
           => ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( ( r1_lattice3(A,C,D)
                   => r1_lattice3(A,B,D) )
                  & ( r2_lattice3(A,C,D)
                   => r2_lattice3(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

tff(c_68,plain,
    ( ~ r1_lattice3('#skF_6','#skF_7','#skF_9')
    | r2_lattice3('#skF_6','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_98,plain,(
    ~ r1_lattice3('#skF_6','#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_62,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_58,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97010,plain,(
    ! [A_3120,B_3121,C_3122] :
      ( r2_hidden('#skF_4'(A_3120,B_3121,C_3122),B_3121)
      | r1_lattice3(A_3120,B_3121,C_3122)
      | ~ m1_subset_1(C_3122,u1_struct_0(A_3120))
      | ~ l1_orders_2(A_3120) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_95411,plain,(
    ! [A_2982,C_2983,B_2984] :
      ( m1_subset_1(A_2982,C_2983)
      | ~ m1_subset_1(B_2984,k1_zfmisc_1(C_2983))
      | ~ r2_hidden(A_2982,B_2984) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_95417,plain,(
    ! [A_2982,B_20,A_19] :
      ( m1_subset_1(A_2982,B_20)
      | ~ r2_hidden(A_2982,A_19)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_32,c_95411])).

tff(c_112992,plain,(
    ! [A_3795,B_3796,C_3797,B_3798] :
      ( m1_subset_1('#skF_4'(A_3795,B_3796,C_3797),B_3798)
      | ~ r1_tarski(B_3796,B_3798)
      | r1_lattice3(A_3795,B_3796,C_3797)
      | ~ m1_subset_1(C_3797,u1_struct_0(A_3795))
      | ~ l1_orders_2(A_3795) ) ),
    inference(resolution,[status(thm)],[c_97010,c_95417])).

tff(c_95502,plain,(
    ! [A_2999,B_3000] :
      ( m1_subset_1(k6_domain_1(A_2999,B_3000),k1_zfmisc_1(A_2999))
      | ~ m1_subset_1(B_3000,A_2999)
      | v1_xboole_0(A_2999) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_95542,plain,(
    ! [A_3002,B_3003] :
      ( r1_tarski(k6_domain_1(A_3002,B_3003),A_3002)
      | ~ m1_subset_1(B_3003,A_3002)
      | v1_xboole_0(A_3002) ) ),
    inference(resolution,[status(thm)],[c_95502,c_30])).

tff(c_60,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_95357,plain,(
    ! [A_2974,C_2975,B_2976] :
      ( r1_tarski(A_2974,C_2975)
      | ~ r1_tarski(B_2976,C_2975)
      | ~ r1_tarski(A_2974,B_2976) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_95366,plain,(
    ! [A_2974] :
      ( r1_tarski(A_2974,'#skF_8')
      | ~ r1_tarski(A_2974,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_60,c_95357])).

tff(c_95567,plain,(
    ! [B_3003] :
      ( r1_tarski(k6_domain_1('#skF_7',B_3003),'#skF_8')
      | ~ m1_subset_1(B_3003,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_95542,c_95366])).

tff(c_95574,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_95567])).

tff(c_96136,plain,(
    ! [A_3065,B_3066,C_3067] :
      ( r2_hidden('#skF_4'(A_3065,B_3066,C_3067),B_3066)
      | r1_lattice3(A_3065,B_3066,C_3067)
      | ~ m1_subset_1(C_3067,u1_struct_0(A_3065))
      | ~ l1_orders_2(A_3065) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96178,plain,(
    ! [B_3068,A_3069,C_3070] :
      ( ~ v1_xboole_0(B_3068)
      | r1_lattice3(A_3069,B_3068,C_3070)
      | ~ m1_subset_1(C_3070,u1_struct_0(A_3069))
      | ~ l1_orders_2(A_3069) ) ),
    inference(resolution,[status(thm)],[c_96136,c_2])).

tff(c_96189,plain,(
    ! [B_3068] :
      ( ~ v1_xboole_0(B_3068)
      | r1_lattice3('#skF_6',B_3068,'#skF_9')
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_96178])).

tff(c_96196,plain,(
    ! [B_3071] :
      ( ~ v1_xboole_0(B_3071)
      | r1_lattice3('#skF_6',B_3071,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_96189])).

tff(c_96199,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_96196,c_98])).

tff(c_96203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95574,c_96199])).

tff(c_96205,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_95567])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | v1_xboole_0(B_18)
      | ~ m1_subset_1(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_95419,plain,(
    ! [A_2985,B_2986,A_2987] :
      ( m1_subset_1(A_2985,B_2986)
      | ~ r2_hidden(A_2985,A_2987)
      | ~ r1_tarski(A_2987,B_2986) ) ),
    inference(resolution,[status(thm)],[c_32,c_95411])).

tff(c_96695,plain,(
    ! [A_3099,B_3100,B_3101] :
      ( m1_subset_1(A_3099,B_3100)
      | ~ r1_tarski(B_3101,B_3100)
      | v1_xboole_0(B_3101)
      | ~ m1_subset_1(A_3099,B_3101) ) ),
    inference(resolution,[status(thm)],[c_28,c_95419])).

tff(c_96713,plain,(
    ! [A_3099] :
      ( m1_subset_1(A_3099,'#skF_8')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_3099,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_60,c_96695])).

tff(c_96726,plain,(
    ! [A_3099] :
      ( m1_subset_1(A_3099,'#skF_8')
      | ~ m1_subset_1(A_3099,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_96205,c_96713])).

tff(c_113120,plain,(
    ! [A_3795,B_3796,C_3797] :
      ( m1_subset_1('#skF_4'(A_3795,B_3796,C_3797),'#skF_8')
      | ~ r1_tarski(B_3796,'#skF_7')
      | r1_lattice3(A_3795,B_3796,C_3797)
      | ~ m1_subset_1(C_3797,u1_struct_0(A_3795))
      | ~ l1_orders_2(A_3795) ) ),
    inference(resolution,[status(thm)],[c_112992,c_96726])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95320,plain,(
    ! [C_2964,B_2965,A_2966] :
      ( ~ v1_xboole_0(C_2964)
      | ~ m1_subset_1(B_2965,k1_zfmisc_1(C_2964))
      | ~ r2_hidden(A_2966,B_2965) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_95328,plain,(
    ! [B_2967,A_2968,A_2969] :
      ( ~ v1_xboole_0(B_2967)
      | ~ r2_hidden(A_2968,A_2969)
      | ~ r1_tarski(A_2969,B_2967) ) ),
    inference(resolution,[status(thm)],[c_32,c_95320])).

tff(c_95344,plain,(
    ! [B_2972,A_2973] :
      ( ~ v1_xboole_0(B_2972)
      | ~ r1_tarski(A_2973,B_2972)
      | v1_xboole_0(A_2973) ) ),
    inference(resolution,[status(thm)],[c_4,c_95328])).

tff(c_95356,plain,
    ( ~ v1_xboole_0('#skF_8')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_95344])).

tff(c_95367,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_95356])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_99043,plain,(
    ! [A_3261,B_3262,C_3263] :
      ( m1_subset_1('#skF_4'(A_3261,B_3262,C_3263),B_3262)
      | r1_lattice3(A_3261,B_3262,C_3263)
      | ~ m1_subset_1(C_3263,u1_struct_0(A_3261))
      | ~ l1_orders_2(A_3261) ) ),
    inference(resolution,[status(thm)],[c_97010,c_26])).

tff(c_99210,plain,(
    ! [A_3270,C_3271] :
      ( m1_subset_1('#skF_4'(A_3270,'#skF_7',C_3271),'#skF_8')
      | r1_lattice3(A_3270,'#skF_7',C_3271)
      | ~ m1_subset_1(C_3271,u1_struct_0(A_3270))
      | ~ l1_orders_2(A_3270) ) ),
    inference(resolution,[status(thm)],[c_99043,c_96726])).

tff(c_40,plain,(
    ! [A_29,B_30] :
      ( k6_domain_1(A_29,B_30) = k1_tarski(B_30)
      | ~ m1_subset_1(B_30,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_99215,plain,(
    ! [A_3270,C_3271] :
      ( k6_domain_1('#skF_8','#skF_4'(A_3270,'#skF_7',C_3271)) = k1_tarski('#skF_4'(A_3270,'#skF_7',C_3271))
      | v1_xboole_0('#skF_8')
      | r1_lattice3(A_3270,'#skF_7',C_3271)
      | ~ m1_subset_1(C_3271,u1_struct_0(A_3270))
      | ~ l1_orders_2(A_3270) ) ),
    inference(resolution,[status(thm)],[c_99210,c_40])).

tff(c_118144,plain,(
    ! [A_3956,C_3957] :
      ( k6_domain_1('#skF_8','#skF_4'(A_3956,'#skF_7',C_3957)) = k1_tarski('#skF_4'(A_3956,'#skF_7',C_3957))
      | r1_lattice3(A_3956,'#skF_7',C_3957)
      | ~ m1_subset_1(C_3957,u1_struct_0(A_3956))
      | ~ l1_orders_2(A_3956) ) ),
    inference(negUnitSimplification,[status(thm)],[c_95367,c_99215])).

tff(c_118209,plain,
    ( k6_domain_1('#skF_8','#skF_4'('#skF_6','#skF_7','#skF_9')) = k1_tarski('#skF_4'('#skF_6','#skF_7','#skF_9'))
    | r1_lattice3('#skF_6','#skF_7','#skF_9')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_118144])).

tff(c_118228,plain,
    ( k6_domain_1('#skF_8','#skF_4'('#skF_6','#skF_7','#skF_9')) = k1_tarski('#skF_4'('#skF_6','#skF_7','#skF_9'))
    | r1_lattice3('#skF_6','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_118209])).

tff(c_118229,plain,(
    k6_domain_1('#skF_8','#skF_4'('#skF_6','#skF_7','#skF_9')) = k1_tarski('#skF_4'('#skF_6','#skF_7','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_118228])).

tff(c_95522,plain,(
    ! [A_2999,B_3000] :
      ( r1_tarski(k6_domain_1(A_2999,B_3000),A_2999)
      | ~ m1_subset_1(B_3000,A_2999)
      | v1_xboole_0(A_2999) ) ),
    inference(resolution,[status(thm)],[c_95502,c_30])).

tff(c_118269,plain,
    ( r1_tarski(k1_tarski('#skF_4'('#skF_6','#skF_7','#skF_9')),'#skF_8')
    | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7','#skF_9'),'#skF_8')
    | v1_xboole_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_118229,c_95522])).

tff(c_118296,plain,
    ( r1_tarski(k1_tarski('#skF_4'('#skF_6','#skF_7','#skF_9')),'#skF_8')
    | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_95367,c_118269])).

tff(c_118299,plain,(
    ~ m1_subset_1('#skF_4'('#skF_6','#skF_7','#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_118296])).

tff(c_118302,plain,
    ( ~ r1_tarski('#skF_7','#skF_7')
    | r1_lattice3('#skF_6','#skF_7','#skF_9')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_113120,c_118299])).

tff(c_118311,plain,(
    r1_lattice3('#skF_6','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_10,c_118302])).

tff(c_118313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_118311])).

tff(c_118315,plain,(
    m1_subset_1('#skF_4'('#skF_6','#skF_7','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_118296])).

tff(c_48683,plain,(
    ! [A_1617,B_1618,C_1619] :
      ( r2_hidden('#skF_4'(A_1617,B_1618,C_1619),B_1618)
      | r1_lattice3(A_1617,B_1618,C_1619)
      | ~ m1_subset_1(C_1619,u1_struct_0(A_1617))
      | ~ l1_orders_2(A_1617) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_47595,plain,(
    ! [A_1524,C_1525,B_1526] :
      ( m1_subset_1(A_1524,C_1525)
      | ~ m1_subset_1(B_1526,k1_zfmisc_1(C_1525))
      | ~ r2_hidden(A_1524,B_1526) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_47601,plain,(
    ! [A_1524,B_20,A_19] :
      ( m1_subset_1(A_1524,B_20)
      | ~ r2_hidden(A_1524,A_19)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_32,c_47595])).

tff(c_66606,plain,(
    ! [A_2362,B_2363,C_2364,B_2365] :
      ( m1_subset_1('#skF_4'(A_2362,B_2363,C_2364),B_2365)
      | ~ r1_tarski(B_2363,B_2365)
      | r1_lattice3(A_2362,B_2363,C_2364)
      | ~ m1_subset_1(C_2364,u1_struct_0(A_2362))
      | ~ l1_orders_2(A_2362) ) ),
    inference(resolution,[status(thm)],[c_48683,c_47601])).

tff(c_47710,plain,(
    ! [A_1544,B_1545] :
      ( m1_subset_1(k6_domain_1(A_1544,B_1545),k1_zfmisc_1(A_1544))
      | ~ m1_subset_1(B_1545,A_1544)
      | v1_xboole_0(A_1544) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_47764,plain,(
    ! [A_1548,B_1549] :
      ( r1_tarski(k6_domain_1(A_1548,B_1549),A_1548)
      | ~ m1_subset_1(B_1549,A_1548)
      | v1_xboole_0(A_1548) ) ),
    inference(resolution,[status(thm)],[c_47710,c_30])).

tff(c_47554,plain,(
    ! [A_1514,C_1515,B_1516] :
      ( r1_tarski(A_1514,C_1515)
      | ~ r1_tarski(B_1516,C_1515)
      | ~ r1_tarski(A_1514,B_1516) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_47563,plain,(
    ! [A_1514] :
      ( r1_tarski(A_1514,'#skF_8')
      | ~ r1_tarski(A_1514,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_60,c_47554])).

tff(c_47790,plain,(
    ! [B_1549] :
      ( r1_tarski(k6_domain_1('#skF_7',B_1549),'#skF_8')
      | ~ m1_subset_1(B_1549,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_47764,c_47563])).

tff(c_47808,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_47790])).

tff(c_48109,plain,(
    ! [A_1582,B_1583,C_1584] :
      ( r2_hidden('#skF_4'(A_1582,B_1583,C_1584),B_1583)
      | r1_lattice3(A_1582,B_1583,C_1584)
      | ~ m1_subset_1(C_1584,u1_struct_0(A_1582))
      | ~ l1_orders_2(A_1582) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_48212,plain,(
    ! [B_1591,A_1592,C_1593] :
      ( ~ v1_xboole_0(B_1591)
      | r1_lattice3(A_1592,B_1591,C_1593)
      | ~ m1_subset_1(C_1593,u1_struct_0(A_1592))
      | ~ l1_orders_2(A_1592) ) ),
    inference(resolution,[status(thm)],[c_48109,c_2])).

tff(c_48220,plain,(
    ! [B_1591] :
      ( ~ v1_xboole_0(B_1591)
      | r1_lattice3('#skF_6',B_1591,'#skF_9')
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_48212])).

tff(c_48226,plain,(
    ! [B_1594] :
      ( ~ v1_xboole_0(B_1594)
      | r1_lattice3('#skF_6',B_1594,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_48220])).

tff(c_48229,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_48226,c_98])).

tff(c_48233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47808,c_48229])).

tff(c_48235,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_47790])).

tff(c_47623,plain,(
    ! [A_1531,B_1532,A_1533] :
      ( m1_subset_1(A_1531,B_1532)
      | ~ r2_hidden(A_1531,A_1533)
      | ~ r1_tarski(A_1533,B_1532) ) ),
    inference(resolution,[status(thm)],[c_32,c_47595])).

tff(c_48745,plain,(
    ! [A_1623,B_1624,B_1625] :
      ( m1_subset_1(A_1623,B_1624)
      | ~ r1_tarski(B_1625,B_1624)
      | v1_xboole_0(B_1625)
      | ~ m1_subset_1(A_1623,B_1625) ) ),
    inference(resolution,[status(thm)],[c_28,c_47623])).

tff(c_48763,plain,(
    ! [A_1623] :
      ( m1_subset_1(A_1623,'#skF_8')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_1623,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_60,c_48745])).

tff(c_48776,plain,(
    ! [A_1623] :
      ( m1_subset_1(A_1623,'#skF_8')
      | ~ m1_subset_1(A_1623,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48235,c_48763])).

tff(c_66738,plain,(
    ! [A_2362,B_2363,C_2364] :
      ( m1_subset_1('#skF_4'(A_2362,B_2363,C_2364),'#skF_8')
      | ~ r1_tarski(B_2363,'#skF_7')
      | r1_lattice3(A_2362,B_2363,C_2364)
      | ~ m1_subset_1(C_2364,u1_struct_0(A_2362))
      | ~ l1_orders_2(A_2362) ) ),
    inference(resolution,[status(thm)],[c_66606,c_48776])).

tff(c_47577,plain,(
    ! [C_1518,B_1519,A_1520] :
      ( ~ v1_xboole_0(C_1518)
      | ~ m1_subset_1(B_1519,k1_zfmisc_1(C_1518))
      | ~ r2_hidden(A_1520,B_1519) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_47585,plain,(
    ! [B_1521,A_1522,A_1523] :
      ( ~ v1_xboole_0(B_1521)
      | ~ r2_hidden(A_1522,A_1523)
      | ~ r1_tarski(A_1523,B_1521) ) ),
    inference(resolution,[status(thm)],[c_32,c_47577])).

tff(c_47609,plain,(
    ! [B_1529,A_1530] :
      ( ~ v1_xboole_0(B_1529)
      | ~ r1_tarski(A_1530,B_1529)
      | v1_xboole_0(A_1530) ) ),
    inference(resolution,[status(thm)],[c_4,c_47585])).

tff(c_47621,plain,
    ( ~ v1_xboole_0('#skF_8')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_47609])).

tff(c_47622,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_47621])).

tff(c_50548,plain,(
    ! [A_1760,B_1761,C_1762] :
      ( m1_subset_1('#skF_4'(A_1760,B_1761,C_1762),B_1761)
      | r1_lattice3(A_1760,B_1761,C_1762)
      | ~ m1_subset_1(C_1762,u1_struct_0(A_1760))
      | ~ l1_orders_2(A_1760) ) ),
    inference(resolution,[status(thm)],[c_48683,c_26])).

tff(c_50719,plain,(
    ! [A_1768,C_1769] :
      ( m1_subset_1('#skF_4'(A_1768,'#skF_7',C_1769),'#skF_8')
      | r1_lattice3(A_1768,'#skF_7',C_1769)
      | ~ m1_subset_1(C_1769,u1_struct_0(A_1768))
      | ~ l1_orders_2(A_1768) ) ),
    inference(resolution,[status(thm)],[c_50548,c_48776])).

tff(c_50722,plain,(
    ! [A_1768,C_1769] :
      ( k6_domain_1('#skF_8','#skF_4'(A_1768,'#skF_7',C_1769)) = k1_tarski('#skF_4'(A_1768,'#skF_7',C_1769))
      | v1_xboole_0('#skF_8')
      | r1_lattice3(A_1768,'#skF_7',C_1769)
      | ~ m1_subset_1(C_1769,u1_struct_0(A_1768))
      | ~ l1_orders_2(A_1768) ) ),
    inference(resolution,[status(thm)],[c_50719,c_40])).

tff(c_68238,plain,(
    ! [A_2431,C_2432] :
      ( k6_domain_1('#skF_8','#skF_4'(A_2431,'#skF_7',C_2432)) = k1_tarski('#skF_4'(A_2431,'#skF_7',C_2432))
      | r1_lattice3(A_2431,'#skF_7',C_2432)
      | ~ m1_subset_1(C_2432,u1_struct_0(A_2431))
      | ~ l1_orders_2(A_2431) ) ),
    inference(negUnitSimplification,[status(thm)],[c_47622,c_50722])).

tff(c_68303,plain,
    ( k6_domain_1('#skF_8','#skF_4'('#skF_6','#skF_7','#skF_9')) = k1_tarski('#skF_4'('#skF_6','#skF_7','#skF_9'))
    | r1_lattice3('#skF_6','#skF_7','#skF_9')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_68238])).

tff(c_68322,plain,
    ( k6_domain_1('#skF_8','#skF_4'('#skF_6','#skF_7','#skF_9')) = k1_tarski('#skF_4'('#skF_6','#skF_7','#skF_9'))
    | r1_lattice3('#skF_6','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_68303])).

tff(c_68323,plain,(
    k6_domain_1('#skF_8','#skF_4'('#skF_6','#skF_7','#skF_9')) = k1_tarski('#skF_4'('#skF_6','#skF_7','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_68322])).

tff(c_47727,plain,(
    ! [A_1544,B_1545] :
      ( r1_tarski(k6_domain_1(A_1544,B_1545),A_1544)
      | ~ m1_subset_1(B_1545,A_1544)
      | v1_xboole_0(A_1544) ) ),
    inference(resolution,[status(thm)],[c_47710,c_30])).

tff(c_68368,plain,
    ( r1_tarski(k1_tarski('#skF_4'('#skF_6','#skF_7','#skF_9')),'#skF_8')
    | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7','#skF_9'),'#skF_8')
    | v1_xboole_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_68323,c_47727])).

tff(c_68395,plain,
    ( r1_tarski(k1_tarski('#skF_4'('#skF_6','#skF_7','#skF_9')),'#skF_8')
    | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_47622,c_68368])).

tff(c_68398,plain,(
    ~ m1_subset_1('#skF_4'('#skF_6','#skF_7','#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_68395])).

tff(c_68401,plain,
    ( ~ r1_tarski('#skF_7','#skF_7')
    | r1_lattice3('#skF_6','#skF_7','#skF_9')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_66738,c_68398])).

tff(c_68410,plain,(
    r1_lattice3('#skF_6','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_10,c_68401])).

tff(c_68412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_68410])).

tff(c_68414,plain,(
    m1_subset_1('#skF_4'('#skF_6','#skF_7','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_68395])).

tff(c_66,plain,
    ( r1_lattice3('#skF_6','#skF_8','#skF_9')
    | ~ r2_lattice3('#skF_6','#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_151,plain,(
    ~ r2_lattice3('#skF_6','#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_1375,plain,(
    ! [A_190,B_191,C_192] :
      ( r2_hidden('#skF_5'(A_190,B_191,C_192),B_191)
      | r2_lattice3(A_190,B_191,C_192)
      | ~ m1_subset_1(C_192,u1_struct_0(A_190))
      | ~ l1_orders_2(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_233,plain,(
    ! [A_96,C_97,B_98] :
      ( m1_subset_1(A_96,C_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(C_97))
      | ~ r2_hidden(A_96,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_239,plain,(
    ! [A_96,B_20,A_19] :
      ( m1_subset_1(A_96,B_20)
      | ~ r2_hidden(A_96,A_19)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_32,c_233])).

tff(c_16976,plain,(
    ! [A_885,B_886,C_887,B_888] :
      ( m1_subset_1('#skF_5'(A_885,B_886,C_887),B_888)
      | ~ r1_tarski(B_886,B_888)
      | r2_lattice3(A_885,B_886,C_887)
      | ~ m1_subset_1(C_887,u1_struct_0(A_885))
      | ~ l1_orders_2(A_885) ) ),
    inference(resolution,[status(thm)],[c_1375,c_239])).

tff(c_344,plain,(
    ! [A_115,B_116] :
      ( m1_subset_1(k6_domain_1(A_115,B_116),k1_zfmisc_1(A_115))
      | ~ m1_subset_1(B_116,A_115)
      | v1_xboole_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_397,plain,(
    ! [A_120,B_121] :
      ( r1_tarski(k6_domain_1(A_120,B_121),A_120)
      | ~ m1_subset_1(B_121,A_120)
      | v1_xboole_0(A_120) ) ),
    inference(resolution,[status(thm)],[c_344,c_30])).

tff(c_186,plain,(
    ! [A_84,C_85,B_86] :
      ( r1_tarski(A_84,C_85)
      | ~ r1_tarski(B_86,C_85)
      | ~ r1_tarski(A_84,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_195,plain,(
    ! [A_84] :
      ( r1_tarski(A_84,'#skF_8')
      | ~ r1_tarski(A_84,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_60,c_186])).

tff(c_423,plain,(
    ! [B_121] :
      ( r1_tarski(k6_domain_1('#skF_7',B_121),'#skF_8')
      | ~ m1_subset_1(B_121,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_397,c_195])).

tff(c_446,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_423])).

tff(c_781,plain,(
    ! [A_154,B_155,C_156] :
      ( r2_hidden('#skF_5'(A_154,B_155,C_156),B_155)
      | r2_lattice3(A_154,B_155,C_156)
      | ~ m1_subset_1(C_156,u1_struct_0(A_154))
      | ~ l1_orders_2(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_844,plain,(
    ! [B_161,A_162,C_163] :
      ( ~ v1_xboole_0(B_161)
      | r2_lattice3(A_162,B_161,C_163)
      | ~ m1_subset_1(C_163,u1_struct_0(A_162))
      | ~ l1_orders_2(A_162) ) ),
    inference(resolution,[status(thm)],[c_781,c_2])).

tff(c_852,plain,(
    ! [B_161] :
      ( ~ v1_xboole_0(B_161)
      | r2_lattice3('#skF_6',B_161,'#skF_9')
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_844])).

tff(c_858,plain,(
    ! [B_164] :
      ( ~ v1_xboole_0(B_164)
      | r2_lattice3('#skF_6',B_164,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_852])).

tff(c_861,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_858,c_151])).

tff(c_865,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_861])).

tff(c_867,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_423])).

tff(c_283,plain,(
    ! [A_104,B_105,A_106] :
      ( m1_subset_1(A_104,B_105)
      | ~ r2_hidden(A_104,A_106)
      | ~ r1_tarski(A_106,B_105) ) ),
    inference(resolution,[status(thm)],[c_32,c_233])).

tff(c_1463,plain,(
    ! [A_199,B_200,B_201] :
      ( m1_subset_1(A_199,B_200)
      | ~ r1_tarski(B_201,B_200)
      | v1_xboole_0(B_201)
      | ~ m1_subset_1(A_199,B_201) ) ),
    inference(resolution,[status(thm)],[c_28,c_283])).

tff(c_1481,plain,(
    ! [A_199] :
      ( m1_subset_1(A_199,'#skF_8')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_199,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_60,c_1463])).

tff(c_1494,plain,(
    ! [A_199] :
      ( m1_subset_1(A_199,'#skF_8')
      | ~ m1_subset_1(A_199,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_867,c_1481])).

tff(c_17104,plain,(
    ! [A_885,B_886,C_887] :
      ( m1_subset_1('#skF_5'(A_885,B_886,C_887),'#skF_8')
      | ~ r1_tarski(B_886,'#skF_7')
      | r2_lattice3(A_885,B_886,C_887)
      | ~ m1_subset_1(C_887,u1_struct_0(A_885))
      | ~ l1_orders_2(A_885) ) ),
    inference(resolution,[status(thm)],[c_16976,c_1494])).

tff(c_209,plain,(
    ! [C_88,B_89,A_90] :
      ( ~ v1_xboole_0(C_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(C_88))
      | ~ r2_hidden(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_217,plain,(
    ! [B_91,A_92,A_93] :
      ( ~ v1_xboole_0(B_91)
      | ~ r2_hidden(A_92,A_93)
      | ~ r1_tarski(A_93,B_91) ) ),
    inference(resolution,[status(thm)],[c_32,c_209])).

tff(c_241,plain,(
    ! [B_99,A_100] :
      ( ~ v1_xboole_0(B_99)
      | ~ r1_tarski(A_100,B_99)
      | v1_xboole_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_4,c_217])).

tff(c_253,plain,
    ( ~ v1_xboole_0('#skF_8')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_241])).

tff(c_254,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_3281,plain,(
    ! [A_329,B_330,C_331] :
      ( m1_subset_1('#skF_5'(A_329,B_330,C_331),B_330)
      | r2_lattice3(A_329,B_330,C_331)
      | ~ m1_subset_1(C_331,u1_struct_0(A_329))
      | ~ l1_orders_2(A_329) ) ),
    inference(resolution,[status(thm)],[c_1375,c_26])).

tff(c_3334,plain,(
    ! [A_334,C_335] :
      ( m1_subset_1('#skF_5'(A_334,'#skF_7',C_335),'#skF_8')
      | r2_lattice3(A_334,'#skF_7',C_335)
      | ~ m1_subset_1(C_335,u1_struct_0(A_334))
      | ~ l1_orders_2(A_334) ) ),
    inference(resolution,[status(thm)],[c_3281,c_1494])).

tff(c_3337,plain,(
    ! [A_334,C_335] :
      ( k6_domain_1('#skF_8','#skF_5'(A_334,'#skF_7',C_335)) = k1_tarski('#skF_5'(A_334,'#skF_7',C_335))
      | v1_xboole_0('#skF_8')
      | r2_lattice3(A_334,'#skF_7',C_335)
      | ~ m1_subset_1(C_335,u1_struct_0(A_334))
      | ~ l1_orders_2(A_334) ) ),
    inference(resolution,[status(thm)],[c_3334,c_40])).

tff(c_20504,plain,(
    ! [A_975,C_976] :
      ( k6_domain_1('#skF_8','#skF_5'(A_975,'#skF_7',C_976)) = k1_tarski('#skF_5'(A_975,'#skF_7',C_976))
      | r2_lattice3(A_975,'#skF_7',C_976)
      | ~ m1_subset_1(C_976,u1_struct_0(A_975))
      | ~ l1_orders_2(A_975) ) ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_3337])).

tff(c_20569,plain,
    ( k6_domain_1('#skF_8','#skF_5'('#skF_6','#skF_7','#skF_9')) = k1_tarski('#skF_5'('#skF_6','#skF_7','#skF_9'))
    | r2_lattice3('#skF_6','#skF_7','#skF_9')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_20504])).

tff(c_20588,plain,
    ( k6_domain_1('#skF_8','#skF_5'('#skF_6','#skF_7','#skF_9')) = k1_tarski('#skF_5'('#skF_6','#skF_7','#skF_9'))
    | r2_lattice3('#skF_6','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_20569])).

tff(c_20589,plain,(
    k6_domain_1('#skF_8','#skF_5'('#skF_6','#skF_7','#skF_9')) = k1_tarski('#skF_5'('#skF_6','#skF_7','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_20588])).

tff(c_364,plain,(
    ! [A_115,B_116] :
      ( r1_tarski(k6_domain_1(A_115,B_116),A_115)
      | ~ m1_subset_1(B_116,A_115)
      | v1_xboole_0(A_115) ) ),
    inference(resolution,[status(thm)],[c_344,c_30])).

tff(c_20629,plain,
    ( r1_tarski(k1_tarski('#skF_5'('#skF_6','#skF_7','#skF_9')),'#skF_8')
    | ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_9'),'#skF_8')
    | v1_xboole_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_20589,c_364])).

tff(c_20656,plain,
    ( r1_tarski(k1_tarski('#skF_5'('#skF_6','#skF_7','#skF_9')),'#skF_8')
    | ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_20629])).

tff(c_20659,plain,(
    ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_20656])).

tff(c_20662,plain,
    ( ~ r1_tarski('#skF_7','#skF_7')
    | r2_lattice3('#skF_6','#skF_7','#skF_9')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_17104,c_20659])).

tff(c_20671,plain,(
    r2_lattice3('#skF_6','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_10,c_20662])).

tff(c_20673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_20671])).

tff(c_20675,plain,(
    m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_20656])).

tff(c_70,plain,
    ( r1_lattice3('#skF_6','#skF_8','#skF_9')
    | r2_lattice3('#skF_6','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_152,plain,(
    r2_lattice3('#skF_6','#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_56,plain,(
    ! [A_43,B_50,C_51] :
      ( m1_subset_1('#skF_5'(A_43,B_50,C_51),u1_struct_0(A_43))
      | r2_lattice3(A_43,B_50,C_51)
      | ~ m1_subset_1(C_51,u1_struct_0(A_43))
      | ~ l1_orders_2(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2614,plain,(
    ! [A_293,D_294,C_295,B_296] :
      ( r1_orders_2(A_293,D_294,C_295)
      | ~ r2_hidden(D_294,B_296)
      | ~ m1_subset_1(D_294,u1_struct_0(A_293))
      | ~ r2_lattice3(A_293,B_296,C_295)
      | ~ m1_subset_1(C_295,u1_struct_0(A_293))
      | ~ l1_orders_2(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6063,plain,(
    ! [A_460,A_461,C_462,B_463] :
      ( r1_orders_2(A_460,A_461,C_462)
      | ~ m1_subset_1(A_461,u1_struct_0(A_460))
      | ~ r2_lattice3(A_460,B_463,C_462)
      | ~ m1_subset_1(C_462,u1_struct_0(A_460))
      | ~ l1_orders_2(A_460)
      | v1_xboole_0(B_463)
      | ~ m1_subset_1(A_461,B_463) ) ),
    inference(resolution,[status(thm)],[c_28,c_2614])).

tff(c_46382,plain,(
    ! [C_1423,B_1425,A_1424,C_1421,B_1422] :
      ( r1_orders_2(A_1424,'#skF_5'(A_1424,B_1422,C_1421),C_1423)
      | ~ r2_lattice3(A_1424,B_1425,C_1423)
      | ~ m1_subset_1(C_1423,u1_struct_0(A_1424))
      | v1_xboole_0(B_1425)
      | ~ m1_subset_1('#skF_5'(A_1424,B_1422,C_1421),B_1425)
      | r2_lattice3(A_1424,B_1422,C_1421)
      | ~ m1_subset_1(C_1421,u1_struct_0(A_1424))
      | ~ l1_orders_2(A_1424) ) ),
    inference(resolution,[status(thm)],[c_56,c_6063])).

tff(c_46404,plain,(
    ! [B_1422,C_1421] :
      ( r1_orders_2('#skF_6','#skF_5'('#skF_6',B_1422,C_1421),'#skF_9')
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1('#skF_5'('#skF_6',B_1422,C_1421),'#skF_8')
      | r2_lattice3('#skF_6',B_1422,C_1421)
      | ~ m1_subset_1(C_1421,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_152,c_46382])).

tff(c_46421,plain,(
    ! [B_1422,C_1421] :
      ( r1_orders_2('#skF_6','#skF_5'('#skF_6',B_1422,C_1421),'#skF_9')
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1('#skF_5'('#skF_6',B_1422,C_1421),'#skF_8')
      | r2_lattice3('#skF_6',B_1422,C_1421)
      | ~ m1_subset_1(C_1421,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_46404])).

tff(c_46626,plain,(
    ! [B_1430,C_1431] :
      ( r1_orders_2('#skF_6','#skF_5'('#skF_6',B_1430,C_1431),'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_6',B_1430,C_1431),'#skF_8')
      | r2_lattice3('#skF_6',B_1430,C_1431)
      | ~ m1_subset_1(C_1431,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_46421])).

tff(c_52,plain,(
    ! [A_43,B_50,C_51] :
      ( ~ r1_orders_2(A_43,'#skF_5'(A_43,B_50,C_51),C_51)
      | r2_lattice3(A_43,B_50,C_51)
      | ~ m1_subset_1(C_51,u1_struct_0(A_43))
      | ~ l1_orders_2(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_46630,plain,(
    ! [B_1430] :
      ( ~ l1_orders_2('#skF_6')
      | ~ m1_subset_1('#skF_5'('#skF_6',B_1430,'#skF_9'),'#skF_8')
      | r2_lattice3('#skF_6',B_1430,'#skF_9')
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_46626,c_52])).

tff(c_46644,plain,(
    ! [B_1432] :
      ( ~ m1_subset_1('#skF_5'('#skF_6',B_1432,'#skF_9'),'#skF_8')
      | r2_lattice3('#skF_6',B_1432,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_46630])).

tff(c_46666,plain,(
    r2_lattice3('#skF_6','#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_20675,c_46644])).

tff(c_46701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_46666])).

tff(c_46702,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_47200,plain,(
    ! [A_1478,B_1479,C_1480] :
      ( r2_hidden('#skF_4'(A_1478,B_1479,C_1480),B_1479)
      | r1_lattice3(A_1478,B_1479,C_1480)
      | ~ m1_subset_1(C_1480,u1_struct_0(A_1478))
      | ~ l1_orders_2(A_1478) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_47497,plain,(
    ! [B_1505,A_1506,C_1507] :
      ( ~ v1_xboole_0(B_1505)
      | r1_lattice3(A_1506,B_1505,C_1507)
      | ~ m1_subset_1(C_1507,u1_struct_0(A_1506))
      | ~ l1_orders_2(A_1506) ) ),
    inference(resolution,[status(thm)],[c_47200,c_2])).

tff(c_47505,plain,(
    ! [B_1505] :
      ( ~ v1_xboole_0(B_1505)
      | r1_lattice3('#skF_6',B_1505,'#skF_9')
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_47497])).

tff(c_47511,plain,(
    ! [B_1508] :
      ( ~ v1_xboole_0(B_1508)
      | r1_lattice3('#skF_6',B_1508,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_47505])).

tff(c_47514,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_47511,c_98])).

tff(c_47518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46702,c_47514])).

tff(c_47519,plain,(
    r1_lattice3('#skF_6','#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_48,plain,(
    ! [A_31,B_38,C_39] :
      ( m1_subset_1('#skF_4'(A_31,B_38,C_39),u1_struct_0(A_31))
      | r1_lattice3(A_31,B_38,C_39)
      | ~ m1_subset_1(C_39,u1_struct_0(A_31))
      | ~ l1_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_49937,plain,(
    ! [A_1724,C_1725,D_1726,B_1727] :
      ( r1_orders_2(A_1724,C_1725,D_1726)
      | ~ r2_hidden(D_1726,B_1727)
      | ~ m1_subset_1(D_1726,u1_struct_0(A_1724))
      | ~ r1_lattice3(A_1724,B_1727,C_1725)
      | ~ m1_subset_1(C_1725,u1_struct_0(A_1724))
      | ~ l1_orders_2(A_1724) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_53704,plain,(
    ! [A_1915,C_1916,A_1917,B_1918] :
      ( r1_orders_2(A_1915,C_1916,A_1917)
      | ~ m1_subset_1(A_1917,u1_struct_0(A_1915))
      | ~ r1_lattice3(A_1915,B_1918,C_1916)
      | ~ m1_subset_1(C_1916,u1_struct_0(A_1915))
      | ~ l1_orders_2(A_1915)
      | v1_xboole_0(B_1918)
      | ~ m1_subset_1(A_1917,B_1918) ) ),
    inference(resolution,[status(thm)],[c_28,c_49937])).

tff(c_94191,plain,(
    ! [C_2878,B_2875,C_2874,B_2876,A_2877] :
      ( r1_orders_2(A_2877,C_2874,'#skF_4'(A_2877,B_2876,C_2878))
      | ~ r1_lattice3(A_2877,B_2875,C_2874)
      | ~ m1_subset_1(C_2874,u1_struct_0(A_2877))
      | v1_xboole_0(B_2875)
      | ~ m1_subset_1('#skF_4'(A_2877,B_2876,C_2878),B_2875)
      | r1_lattice3(A_2877,B_2876,C_2878)
      | ~ m1_subset_1(C_2878,u1_struct_0(A_2877))
      | ~ l1_orders_2(A_2877) ) ),
    inference(resolution,[status(thm)],[c_48,c_53704])).

tff(c_94213,plain,(
    ! [B_2876,C_2878] :
      ( r1_orders_2('#skF_6','#skF_9','#skF_4'('#skF_6',B_2876,C_2878))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_6',B_2876,C_2878),'#skF_8')
      | r1_lattice3('#skF_6',B_2876,C_2878)
      | ~ m1_subset_1(C_2878,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_47519,c_94191])).

tff(c_94230,plain,(
    ! [B_2876,C_2878] :
      ( r1_orders_2('#skF_6','#skF_9','#skF_4'('#skF_6',B_2876,C_2878))
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_6',B_2876,C_2878),'#skF_8')
      | r1_lattice3('#skF_6',B_2876,C_2878)
      | ~ m1_subset_1(C_2878,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_94213])).

tff(c_94410,plain,(
    ! [B_2882,C_2883] :
      ( r1_orders_2('#skF_6','#skF_9','#skF_4'('#skF_6',B_2882,C_2883))
      | ~ m1_subset_1('#skF_4'('#skF_6',B_2882,C_2883),'#skF_8')
      | r1_lattice3('#skF_6',B_2882,C_2883)
      | ~ m1_subset_1(C_2883,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_47622,c_94230])).

tff(c_44,plain,(
    ! [A_31,C_39,B_38] :
      ( ~ r1_orders_2(A_31,C_39,'#skF_4'(A_31,B_38,C_39))
      | r1_lattice3(A_31,B_38,C_39)
      | ~ m1_subset_1(C_39,u1_struct_0(A_31))
      | ~ l1_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_94414,plain,(
    ! [B_2882] :
      ( ~ l1_orders_2('#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_6',B_2882,'#skF_9'),'#skF_8')
      | r1_lattice3('#skF_6',B_2882,'#skF_9')
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_94410,c_44])).

tff(c_94428,plain,(
    ! [B_2884] :
      ( ~ m1_subset_1('#skF_4'('#skF_6',B_2884,'#skF_9'),'#skF_8')
      | r1_lattice3('#skF_6',B_2884,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_94414])).

tff(c_94450,plain,(
    r1_lattice3('#skF_6','#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_68414,c_94428])).

tff(c_94485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_94450])).

tff(c_94486,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_47621])).

tff(c_94984,plain,(
    ! [A_2930,B_2931,C_2932] :
      ( r2_hidden('#skF_4'(A_2930,B_2931,C_2932),B_2931)
      | r1_lattice3(A_2930,B_2931,C_2932)
      | ~ m1_subset_1(C_2932,u1_struct_0(A_2930))
      | ~ l1_orders_2(A_2930) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_95257,plain,(
    ! [B_2955,A_2956,C_2957] :
      ( ~ v1_xboole_0(B_2955)
      | r1_lattice3(A_2956,B_2955,C_2957)
      | ~ m1_subset_1(C_2957,u1_struct_0(A_2956))
      | ~ l1_orders_2(A_2956) ) ),
    inference(resolution,[status(thm)],[c_94984,c_2])).

tff(c_95267,plain,(
    ! [B_2955] :
      ( ~ v1_xboole_0(B_2955)
      | r1_lattice3('#skF_6',B_2955,'#skF_9')
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_95257])).

tff(c_95274,plain,(
    ! [B_2958] :
      ( ~ v1_xboole_0(B_2958)
      | r1_lattice3('#skF_6',B_2958,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_95267])).

tff(c_95277,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_95274,c_98])).

tff(c_95281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94486,c_95277])).

tff(c_95282,plain,(
    r1_lattice3('#skF_6','#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_98322,plain,(
    ! [A_3219,C_3220,D_3221,B_3222] :
      ( r1_orders_2(A_3219,C_3220,D_3221)
      | ~ r2_hidden(D_3221,B_3222)
      | ~ m1_subset_1(D_3221,u1_struct_0(A_3219))
      | ~ r1_lattice3(A_3219,B_3222,C_3220)
      | ~ m1_subset_1(C_3220,u1_struct_0(A_3219))
      | ~ l1_orders_2(A_3219) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_101748,plain,(
    ! [A_3397,C_3398,A_3399,B_3400] :
      ( r1_orders_2(A_3397,C_3398,A_3399)
      | ~ m1_subset_1(A_3399,u1_struct_0(A_3397))
      | ~ r1_lattice3(A_3397,B_3400,C_3398)
      | ~ m1_subset_1(C_3398,u1_struct_0(A_3397))
      | ~ l1_orders_2(A_3397)
      | v1_xboole_0(B_3400)
      | ~ m1_subset_1(A_3399,B_3400) ) ),
    inference(resolution,[status(thm)],[c_28,c_98322])).

tff(c_148104,plain,(
    ! [B_4442,C_4444,C_4445,A_4443,B_4441] :
      ( r1_orders_2(A_4443,C_4445,'#skF_4'(A_4443,B_4442,C_4444))
      | ~ r1_lattice3(A_4443,B_4441,C_4445)
      | ~ m1_subset_1(C_4445,u1_struct_0(A_4443))
      | v1_xboole_0(B_4441)
      | ~ m1_subset_1('#skF_4'(A_4443,B_4442,C_4444),B_4441)
      | r1_lattice3(A_4443,B_4442,C_4444)
      | ~ m1_subset_1(C_4444,u1_struct_0(A_4443))
      | ~ l1_orders_2(A_4443) ) ),
    inference(resolution,[status(thm)],[c_48,c_101748])).

tff(c_148126,plain,(
    ! [B_4442,C_4444] :
      ( r1_orders_2('#skF_6','#skF_9','#skF_4'('#skF_6',B_4442,C_4444))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_6',B_4442,C_4444),'#skF_8')
      | r1_lattice3('#skF_6',B_4442,C_4444)
      | ~ m1_subset_1(C_4444,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_95282,c_148104])).

tff(c_148143,plain,(
    ! [B_4442,C_4444] :
      ( r1_orders_2('#skF_6','#skF_9','#skF_4'('#skF_6',B_4442,C_4444))
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_6',B_4442,C_4444),'#skF_8')
      | r1_lattice3('#skF_6',B_4442,C_4444)
      | ~ m1_subset_1(C_4444,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_148126])).

tff(c_148361,plain,(
    ! [B_4449,C_4450] :
      ( r1_orders_2('#skF_6','#skF_9','#skF_4'('#skF_6',B_4449,C_4450))
      | ~ m1_subset_1('#skF_4'('#skF_6',B_4449,C_4450),'#skF_8')
      | r1_lattice3('#skF_6',B_4449,C_4450)
      | ~ m1_subset_1(C_4450,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_95367,c_148143])).

tff(c_148365,plain,(
    ! [B_4449] :
      ( ~ l1_orders_2('#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_6',B_4449,'#skF_9'),'#skF_8')
      | r1_lattice3('#skF_6',B_4449,'#skF_9')
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_148361,c_44])).

tff(c_148379,plain,(
    ! [B_4451] :
      ( ~ m1_subset_1('#skF_4'('#skF_6',B_4451,'#skF_9'),'#skF_8')
      | r1_lattice3('#skF_6',B_4451,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_148365])).

tff(c_148398,plain,(
    r1_lattice3('#skF_6','#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_118315,c_148379])).

tff(c_148436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_148398])).

tff(c_148437,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_95356])).

tff(c_149105,plain,(
    ! [A_4516,B_4517,C_4518] :
      ( r2_hidden('#skF_4'(A_4516,B_4517,C_4518),B_4517)
      | r1_lattice3(A_4516,B_4517,C_4518)
      | ~ m1_subset_1(C_4518,u1_struct_0(A_4516))
      | ~ l1_orders_2(A_4516) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_149309,plain,(
    ! [B_4534,A_4535,C_4536] :
      ( ~ v1_xboole_0(B_4534)
      | r1_lattice3(A_4535,B_4534,C_4536)
      | ~ m1_subset_1(C_4536,u1_struct_0(A_4535))
      | ~ l1_orders_2(A_4535) ) ),
    inference(resolution,[status(thm)],[c_149105,c_2])).

tff(c_149322,plain,(
    ! [B_4534] :
      ( ~ v1_xboole_0(B_4534)
      | r1_lattice3('#skF_6',B_4534,'#skF_9')
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_149309])).

tff(c_149330,plain,(
    ! [B_4537] :
      ( ~ v1_xboole_0(B_4537)
      | r1_lattice3('#skF_6',B_4537,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_149322])).

tff(c_149333,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_149330,c_98])).

tff(c_149337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148437,c_149333])).

tff(c_149339,plain,(
    r1_lattice3('#skF_6','#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_64,plain,
    ( ~ r1_lattice3('#skF_6','#skF_7','#skF_9')
    | ~ r2_lattice3('#skF_6','#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_149383,plain,(
    ~ r2_lattice3('#skF_6','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149339,c_64])).

tff(c_151010,plain,(
    ! [A_4692,B_4693,C_4694] :
      ( r2_hidden('#skF_5'(A_4692,B_4693,C_4694),B_4693)
      | r2_lattice3(A_4692,B_4693,C_4694)
      | ~ m1_subset_1(C_4694,u1_struct_0(A_4692))
      | ~ l1_orders_2(A_4692) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_149469,plain,(
    ! [A_4564,C_4565,B_4566] :
      ( m1_subset_1(A_4564,C_4565)
      | ~ m1_subset_1(B_4566,k1_zfmisc_1(C_4565))
      | ~ r2_hidden(A_4564,B_4566) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_149475,plain,(
    ! [A_4564,B_20,A_19] :
      ( m1_subset_1(A_4564,B_20)
      | ~ r2_hidden(A_4564,A_19)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_32,c_149469])).

tff(c_168366,plain,(
    ! [A_5417,B_5418,C_5419,B_5420] :
      ( m1_subset_1('#skF_5'(A_5417,B_5418,C_5419),B_5420)
      | ~ r1_tarski(B_5418,B_5420)
      | r2_lattice3(A_5417,B_5418,C_5419)
      | ~ m1_subset_1(C_5419,u1_struct_0(A_5417))
      | ~ l1_orders_2(A_5417) ) ),
    inference(resolution,[status(thm)],[c_151010,c_149475])).

tff(c_149584,plain,(
    ! [A_4584,B_4585] :
      ( m1_subset_1(k6_domain_1(A_4584,B_4585),k1_zfmisc_1(A_4584))
      | ~ m1_subset_1(B_4585,A_4584)
      | v1_xboole_0(A_4584) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_149638,plain,(
    ! [A_4588,B_4589] :
      ( r1_tarski(k6_domain_1(A_4588,B_4589),A_4588)
      | ~ m1_subset_1(B_4589,A_4588)
      | v1_xboole_0(A_4588) ) ),
    inference(resolution,[status(thm)],[c_149584,c_30])).

tff(c_149428,plain,(
    ! [A_4554,C_4555,B_4556] :
      ( r1_tarski(A_4554,C_4555)
      | ~ r1_tarski(B_4556,C_4555)
      | ~ r1_tarski(A_4554,B_4556) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_149437,plain,(
    ! [A_4554] :
      ( r1_tarski(A_4554,'#skF_8')
      | ~ r1_tarski(A_4554,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_60,c_149428])).

tff(c_149664,plain,(
    ! [B_4589] :
      ( r1_tarski(k6_domain_1('#skF_7',B_4589),'#skF_8')
      | ~ m1_subset_1(B_4589,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_149638,c_149437])).

tff(c_149682,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_149664])).

tff(c_150129,plain,(
    ! [A_4637,B_4638,C_4639] :
      ( r2_hidden('#skF_5'(A_4637,B_4638,C_4639),B_4638)
      | r2_lattice3(A_4637,B_4638,C_4639)
      | ~ m1_subset_1(C_4639,u1_struct_0(A_4637))
      | ~ l1_orders_2(A_4637) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_150191,plain,(
    ! [B_4642,A_4643,C_4644] :
      ( ~ v1_xboole_0(B_4642)
      | r2_lattice3(A_4643,B_4642,C_4644)
      | ~ m1_subset_1(C_4644,u1_struct_0(A_4643))
      | ~ l1_orders_2(A_4643) ) ),
    inference(resolution,[status(thm)],[c_150129,c_2])).

tff(c_150202,plain,(
    ! [B_4642] :
      ( ~ v1_xboole_0(B_4642)
      | r2_lattice3('#skF_6',B_4642,'#skF_9')
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_150191])).

tff(c_150209,plain,(
    ! [B_4645] :
      ( ~ v1_xboole_0(B_4645)
      | r2_lattice3('#skF_6',B_4645,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_150202])).

tff(c_150212,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_150209,c_149383])).

tff(c_150216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149682,c_150212])).

tff(c_150218,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_149664])).

tff(c_149497,plain,(
    ! [A_4571,B_4572,A_4573] :
      ( m1_subset_1(A_4571,B_4572)
      | ~ r2_hidden(A_4571,A_4573)
      | ~ r1_tarski(A_4573,B_4572) ) ),
    inference(resolution,[status(thm)],[c_32,c_149469])).

tff(c_150700,plain,(
    ! [A_4671,B_4672,B_4673] :
      ( m1_subset_1(A_4671,B_4672)
      | ~ r1_tarski(B_4673,B_4672)
      | v1_xboole_0(B_4673)
      | ~ m1_subset_1(A_4671,B_4673) ) ),
    inference(resolution,[status(thm)],[c_28,c_149497])).

tff(c_150718,plain,(
    ! [A_4671] :
      ( m1_subset_1(A_4671,'#skF_8')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_4671,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_60,c_150700])).

tff(c_150731,plain,(
    ! [A_4671] :
      ( m1_subset_1(A_4671,'#skF_8')
      | ~ m1_subset_1(A_4671,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_150218,c_150718])).

tff(c_168498,plain,(
    ! [A_5417,B_5418,C_5419] :
      ( m1_subset_1('#skF_5'(A_5417,B_5418,C_5419),'#skF_8')
      | ~ r1_tarski(B_5418,'#skF_7')
      | r2_lattice3(A_5417,B_5418,C_5419)
      | ~ m1_subset_1(C_5419,u1_struct_0(A_5417))
      | ~ l1_orders_2(A_5417) ) ),
    inference(resolution,[status(thm)],[c_168366,c_150731])).

tff(c_149451,plain,(
    ! [C_4558,B_4559,A_4560] :
      ( ~ v1_xboole_0(C_4558)
      | ~ m1_subset_1(B_4559,k1_zfmisc_1(C_4558))
      | ~ r2_hidden(A_4560,B_4559) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_149459,plain,(
    ! [B_4561,A_4562,A_4563] :
      ( ~ v1_xboole_0(B_4561)
      | ~ r2_hidden(A_4562,A_4563)
      | ~ r1_tarski(A_4563,B_4561) ) ),
    inference(resolution,[status(thm)],[c_32,c_149451])).

tff(c_149483,plain,(
    ! [B_4569,A_4570] :
      ( ~ v1_xboole_0(B_4569)
      | ~ r1_tarski(A_4570,B_4569)
      | v1_xboole_0(A_4570) ) ),
    inference(resolution,[status(thm)],[c_4,c_149459])).

tff(c_149495,plain,
    ( ~ v1_xboole_0('#skF_8')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_149483])).

tff(c_149496,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_149495])).

tff(c_153141,plain,(
    ! [A_4845,B_4846,C_4847] :
      ( m1_subset_1('#skF_5'(A_4845,B_4846,C_4847),B_4846)
      | r2_lattice3(A_4845,B_4846,C_4847)
      | ~ m1_subset_1(C_4847,u1_struct_0(A_4845))
      | ~ l1_orders_2(A_4845) ) ),
    inference(resolution,[status(thm)],[c_151010,c_26])).

tff(c_153284,plain,(
    ! [A_4851,C_4852] :
      ( m1_subset_1('#skF_5'(A_4851,'#skF_7',C_4852),'#skF_8')
      | r2_lattice3(A_4851,'#skF_7',C_4852)
      | ~ m1_subset_1(C_4852,u1_struct_0(A_4851))
      | ~ l1_orders_2(A_4851) ) ),
    inference(resolution,[status(thm)],[c_153141,c_150731])).

tff(c_153289,plain,(
    ! [A_4851,C_4852] :
      ( k6_domain_1('#skF_8','#skF_5'(A_4851,'#skF_7',C_4852)) = k1_tarski('#skF_5'(A_4851,'#skF_7',C_4852))
      | v1_xboole_0('#skF_8')
      | r2_lattice3(A_4851,'#skF_7',C_4852)
      | ~ m1_subset_1(C_4852,u1_struct_0(A_4851))
      | ~ l1_orders_2(A_4851) ) ),
    inference(resolution,[status(thm)],[c_153284,c_40])).

tff(c_172282,plain,(
    ! [A_5542,C_5543] :
      ( k6_domain_1('#skF_8','#skF_5'(A_5542,'#skF_7',C_5543)) = k1_tarski('#skF_5'(A_5542,'#skF_7',C_5543))
      | r2_lattice3(A_5542,'#skF_7',C_5543)
      | ~ m1_subset_1(C_5543,u1_struct_0(A_5542))
      | ~ l1_orders_2(A_5542) ) ),
    inference(negUnitSimplification,[status(thm)],[c_149496,c_153289])).

tff(c_172347,plain,
    ( k6_domain_1('#skF_8','#skF_5'('#skF_6','#skF_7','#skF_9')) = k1_tarski('#skF_5'('#skF_6','#skF_7','#skF_9'))
    | r2_lattice3('#skF_6','#skF_7','#skF_9')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_172282])).

tff(c_172366,plain,
    ( k6_domain_1('#skF_8','#skF_5'('#skF_6','#skF_7','#skF_9')) = k1_tarski('#skF_5'('#skF_6','#skF_7','#skF_9'))
    | r2_lattice3('#skF_6','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_172347])).

tff(c_172367,plain,(
    k6_domain_1('#skF_8','#skF_5'('#skF_6','#skF_7','#skF_9')) = k1_tarski('#skF_5'('#skF_6','#skF_7','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_149383,c_172366])).

tff(c_149601,plain,(
    ! [A_4584,B_4585] :
      ( r1_tarski(k6_domain_1(A_4584,B_4585),A_4584)
      | ~ m1_subset_1(B_4585,A_4584)
      | v1_xboole_0(A_4584) ) ),
    inference(resolution,[status(thm)],[c_149584,c_30])).

tff(c_172407,plain,
    ( r1_tarski(k1_tarski('#skF_5'('#skF_6','#skF_7','#skF_9')),'#skF_8')
    | ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_9'),'#skF_8')
    | v1_xboole_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_172367,c_149601])).

tff(c_172434,plain,
    ( r1_tarski(k1_tarski('#skF_5'('#skF_6','#skF_7','#skF_9')),'#skF_8')
    | ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_149496,c_172407])).

tff(c_172437,plain,(
    ~ m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_172434])).

tff(c_172440,plain,
    ( ~ r1_tarski('#skF_7','#skF_7')
    | r2_lattice3('#skF_6','#skF_7','#skF_9')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_168498,c_172437])).

tff(c_172449,plain,(
    r2_lattice3('#skF_6','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_10,c_172440])).

tff(c_172451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149383,c_172449])).

tff(c_172453,plain,(
    m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_172434])).

tff(c_149338,plain,(
    r2_lattice3('#skF_6','#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_152161,plain,(
    ! [A_4782,D_4783,C_4784,B_4785] :
      ( r1_orders_2(A_4782,D_4783,C_4784)
      | ~ r2_hidden(D_4783,B_4785)
      | ~ m1_subset_1(D_4783,u1_struct_0(A_4782))
      | ~ r2_lattice3(A_4782,B_4785,C_4784)
      | ~ m1_subset_1(C_4784,u1_struct_0(A_4782))
      | ~ l1_orders_2(A_4782) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_156124,plain,(
    ! [A_4982,A_4983,C_4984,B_4985] :
      ( r1_orders_2(A_4982,A_4983,C_4984)
      | ~ m1_subset_1(A_4983,u1_struct_0(A_4982))
      | ~ r2_lattice3(A_4982,B_4985,C_4984)
      | ~ m1_subset_1(C_4984,u1_struct_0(A_4982))
      | ~ l1_orders_2(A_4982)
      | v1_xboole_0(B_4985)
      | ~ m1_subset_1(A_4983,B_4985) ) ),
    inference(resolution,[status(thm)],[c_28,c_152161])).

tff(c_202942,plain,(
    ! [A_6034,B_6033,B_6032,C_6035,C_6031] :
      ( r1_orders_2(A_6034,'#skF_5'(A_6034,B_6033,C_6031),C_6035)
      | ~ r2_lattice3(A_6034,B_6032,C_6035)
      | ~ m1_subset_1(C_6035,u1_struct_0(A_6034))
      | v1_xboole_0(B_6032)
      | ~ m1_subset_1('#skF_5'(A_6034,B_6033,C_6031),B_6032)
      | r2_lattice3(A_6034,B_6033,C_6031)
      | ~ m1_subset_1(C_6031,u1_struct_0(A_6034))
      | ~ l1_orders_2(A_6034) ) ),
    inference(resolution,[status(thm)],[c_56,c_156124])).

tff(c_202964,plain,(
    ! [B_6033,C_6031] :
      ( r1_orders_2('#skF_6','#skF_5'('#skF_6',B_6033,C_6031),'#skF_9')
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1('#skF_5'('#skF_6',B_6033,C_6031),'#skF_8')
      | r2_lattice3('#skF_6',B_6033,C_6031)
      | ~ m1_subset_1(C_6031,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_149338,c_202942])).

tff(c_202981,plain,(
    ! [B_6033,C_6031] :
      ( r1_orders_2('#skF_6','#skF_5'('#skF_6',B_6033,C_6031),'#skF_9')
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1('#skF_5'('#skF_6',B_6033,C_6031),'#skF_8')
      | r2_lattice3('#skF_6',B_6033,C_6031)
      | ~ m1_subset_1(C_6031,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_202964])).

tff(c_203063,plain,(
    ! [B_6039,C_6040] :
      ( r1_orders_2('#skF_6','#skF_5'('#skF_6',B_6039,C_6040),'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_6',B_6039,C_6040),'#skF_8')
      | r2_lattice3('#skF_6',B_6039,C_6040)
      | ~ m1_subset_1(C_6040,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_149496,c_202981])).

tff(c_203067,plain,(
    ! [B_6039] :
      ( ~ l1_orders_2('#skF_6')
      | ~ m1_subset_1('#skF_5'('#skF_6',B_6039,'#skF_9'),'#skF_8')
      | r2_lattice3('#skF_6',B_6039,'#skF_9')
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_203063,c_52])).

tff(c_203081,plain,(
    ! [B_6041] :
      ( ~ m1_subset_1('#skF_5'('#skF_6',B_6041,'#skF_9'),'#skF_8')
      | r2_lattice3('#skF_6',B_6041,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_203067])).

tff(c_203100,plain,(
    r2_lattice3('#skF_6','#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_172453,c_203081])).

tff(c_203138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149383,c_203100])).

tff(c_203139,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_149495])).

tff(c_203690,plain,(
    ! [A_6092,B_6093,C_6094] :
      ( r2_hidden('#skF_5'(A_6092,B_6093,C_6094),B_6093)
      | r2_lattice3(A_6092,B_6093,C_6094)
      | ~ m1_subset_1(C_6094,u1_struct_0(A_6092))
      | ~ l1_orders_2(A_6092) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_203956,plain,(
    ! [B_6118,A_6119,C_6120] :
      ( ~ v1_xboole_0(B_6118)
      | r2_lattice3(A_6119,B_6118,C_6120)
      | ~ m1_subset_1(C_6120,u1_struct_0(A_6119))
      | ~ l1_orders_2(A_6119) ) ),
    inference(resolution,[status(thm)],[c_203690,c_2])).

tff(c_203966,plain,(
    ! [B_6118] :
      ( ~ v1_xboole_0(B_6118)
      | r2_lattice3('#skF_6',B_6118,'#skF_9')
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_203956])).

tff(c_203974,plain,(
    ! [B_6124] :
      ( ~ v1_xboole_0(B_6124)
      | r2_lattice3('#skF_6',B_6124,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_203966])).

tff(c_203977,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_203974,c_149383])).

tff(c_203981,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_203139,c_203977])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:54:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 59.70/48.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.70/48.17  
% 59.70/48.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.70/48.17  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2
% 59.70/48.17  
% 59.70/48.17  %Foreground sorts:
% 59.70/48.17  
% 59.70/48.17  
% 59.70/48.17  %Background operators:
% 59.70/48.17  
% 59.70/48.17  
% 59.70/48.17  %Foreground operators:
% 59.70/48.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 59.70/48.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 59.70/48.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 59.70/48.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 59.70/48.17  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 59.70/48.17  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 59.70/48.17  tff('#skF_7', type, '#skF_7': $i).
% 59.70/48.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 59.70/48.17  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 59.70/48.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 59.70/48.17  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 59.70/48.17  tff('#skF_6', type, '#skF_6': $i).
% 59.70/48.17  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 59.70/48.17  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 59.70/48.17  tff('#skF_9', type, '#skF_9': $i).
% 59.70/48.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 59.70/48.17  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 59.70/48.17  tff('#skF_8', type, '#skF_8': $i).
% 59.70/48.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 59.70/48.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 59.70/48.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 59.70/48.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 59.70/48.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 59.70/48.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 59.70/48.17  
% 59.70/48.21  tff(f_136, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_0)).
% 59.70/48.21  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 59.70/48.21  tff(f_105, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 59.70/48.21  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 59.70/48.21  tff(f_70, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 59.70/48.21  tff(f_84, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 59.70/48.21  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 59.70/48.21  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 59.70/48.21  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 59.70/48.21  tff(f_77, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 59.70/48.21  tff(f_54, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 59.70/48.21  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 59.70/48.21  tff(f_119, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 59.70/48.21  tff(c_68, plain, (~r1_lattice3('#skF_6', '#skF_7', '#skF_9') | r2_lattice3('#skF_6', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_136])).
% 59.70/48.21  tff(c_98, plain, (~r1_lattice3('#skF_6', '#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_68])).
% 59.70/48.21  tff(c_62, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_136])).
% 59.70/48.21  tff(c_58, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 59.70/48.21  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 59.70/48.21  tff(c_97010, plain, (![A_3120, B_3121, C_3122]: (r2_hidden('#skF_4'(A_3120, B_3121, C_3122), B_3121) | r1_lattice3(A_3120, B_3121, C_3122) | ~m1_subset_1(C_3122, u1_struct_0(A_3120)) | ~l1_orders_2(A_3120))), inference(cnfTransformation, [status(thm)], [f_105])).
% 59.70/48.21  tff(c_32, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 59.70/48.21  tff(c_95411, plain, (![A_2982, C_2983, B_2984]: (m1_subset_1(A_2982, C_2983) | ~m1_subset_1(B_2984, k1_zfmisc_1(C_2983)) | ~r2_hidden(A_2982, B_2984))), inference(cnfTransformation, [status(thm)], [f_70])).
% 59.70/48.21  tff(c_95417, plain, (![A_2982, B_20, A_19]: (m1_subset_1(A_2982, B_20) | ~r2_hidden(A_2982, A_19) | ~r1_tarski(A_19, B_20))), inference(resolution, [status(thm)], [c_32, c_95411])).
% 59.70/48.21  tff(c_112992, plain, (![A_3795, B_3796, C_3797, B_3798]: (m1_subset_1('#skF_4'(A_3795, B_3796, C_3797), B_3798) | ~r1_tarski(B_3796, B_3798) | r1_lattice3(A_3795, B_3796, C_3797) | ~m1_subset_1(C_3797, u1_struct_0(A_3795)) | ~l1_orders_2(A_3795))), inference(resolution, [status(thm)], [c_97010, c_95417])).
% 59.70/48.21  tff(c_95502, plain, (![A_2999, B_3000]: (m1_subset_1(k6_domain_1(A_2999, B_3000), k1_zfmisc_1(A_2999)) | ~m1_subset_1(B_3000, A_2999) | v1_xboole_0(A_2999))), inference(cnfTransformation, [status(thm)], [f_84])).
% 59.70/48.21  tff(c_30, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 59.70/48.21  tff(c_95542, plain, (![A_3002, B_3003]: (r1_tarski(k6_domain_1(A_3002, B_3003), A_3002) | ~m1_subset_1(B_3003, A_3002) | v1_xboole_0(A_3002))), inference(resolution, [status(thm)], [c_95502, c_30])).
% 59.70/48.21  tff(c_60, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_136])).
% 59.70/48.21  tff(c_95357, plain, (![A_2974, C_2975, B_2976]: (r1_tarski(A_2974, C_2975) | ~r1_tarski(B_2976, C_2975) | ~r1_tarski(A_2974, B_2976))), inference(cnfTransformation, [status(thm)], [f_43])).
% 59.70/48.21  tff(c_95366, plain, (![A_2974]: (r1_tarski(A_2974, '#skF_8') | ~r1_tarski(A_2974, '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_95357])).
% 59.70/48.21  tff(c_95567, plain, (![B_3003]: (r1_tarski(k6_domain_1('#skF_7', B_3003), '#skF_8') | ~m1_subset_1(B_3003, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_95542, c_95366])).
% 59.70/48.21  tff(c_95574, plain, (v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_95567])).
% 59.70/48.21  tff(c_96136, plain, (![A_3065, B_3066, C_3067]: (r2_hidden('#skF_4'(A_3065, B_3066, C_3067), B_3066) | r1_lattice3(A_3065, B_3066, C_3067) | ~m1_subset_1(C_3067, u1_struct_0(A_3065)) | ~l1_orders_2(A_3065))), inference(cnfTransformation, [status(thm)], [f_105])).
% 59.70/48.21  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 59.70/48.21  tff(c_96178, plain, (![B_3068, A_3069, C_3070]: (~v1_xboole_0(B_3068) | r1_lattice3(A_3069, B_3068, C_3070) | ~m1_subset_1(C_3070, u1_struct_0(A_3069)) | ~l1_orders_2(A_3069))), inference(resolution, [status(thm)], [c_96136, c_2])).
% 59.70/48.21  tff(c_96189, plain, (![B_3068]: (~v1_xboole_0(B_3068) | r1_lattice3('#skF_6', B_3068, '#skF_9') | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_96178])).
% 59.70/48.21  tff(c_96196, plain, (![B_3071]: (~v1_xboole_0(B_3071) | r1_lattice3('#skF_6', B_3071, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_96189])).
% 59.70/48.21  tff(c_96199, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_96196, c_98])).
% 59.70/48.21  tff(c_96203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95574, c_96199])).
% 59.70/48.21  tff(c_96205, plain, (~v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_95567])).
% 59.70/48.21  tff(c_28, plain, (![A_17, B_18]: (r2_hidden(A_17, B_18) | v1_xboole_0(B_18) | ~m1_subset_1(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 59.70/48.21  tff(c_95419, plain, (![A_2985, B_2986, A_2987]: (m1_subset_1(A_2985, B_2986) | ~r2_hidden(A_2985, A_2987) | ~r1_tarski(A_2987, B_2986))), inference(resolution, [status(thm)], [c_32, c_95411])).
% 59.70/48.21  tff(c_96695, plain, (![A_3099, B_3100, B_3101]: (m1_subset_1(A_3099, B_3100) | ~r1_tarski(B_3101, B_3100) | v1_xboole_0(B_3101) | ~m1_subset_1(A_3099, B_3101))), inference(resolution, [status(thm)], [c_28, c_95419])).
% 59.70/48.21  tff(c_96713, plain, (![A_3099]: (m1_subset_1(A_3099, '#skF_8') | v1_xboole_0('#skF_7') | ~m1_subset_1(A_3099, '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_96695])).
% 59.70/48.21  tff(c_96726, plain, (![A_3099]: (m1_subset_1(A_3099, '#skF_8') | ~m1_subset_1(A_3099, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_96205, c_96713])).
% 59.70/48.21  tff(c_113120, plain, (![A_3795, B_3796, C_3797]: (m1_subset_1('#skF_4'(A_3795, B_3796, C_3797), '#skF_8') | ~r1_tarski(B_3796, '#skF_7') | r1_lattice3(A_3795, B_3796, C_3797) | ~m1_subset_1(C_3797, u1_struct_0(A_3795)) | ~l1_orders_2(A_3795))), inference(resolution, [status(thm)], [c_112992, c_96726])).
% 59.70/48.21  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 59.70/48.21  tff(c_95320, plain, (![C_2964, B_2965, A_2966]: (~v1_xboole_0(C_2964) | ~m1_subset_1(B_2965, k1_zfmisc_1(C_2964)) | ~r2_hidden(A_2966, B_2965))), inference(cnfTransformation, [status(thm)], [f_77])).
% 59.70/48.21  tff(c_95328, plain, (![B_2967, A_2968, A_2969]: (~v1_xboole_0(B_2967) | ~r2_hidden(A_2968, A_2969) | ~r1_tarski(A_2969, B_2967))), inference(resolution, [status(thm)], [c_32, c_95320])).
% 59.70/48.21  tff(c_95344, plain, (![B_2972, A_2973]: (~v1_xboole_0(B_2972) | ~r1_tarski(A_2973, B_2972) | v1_xboole_0(A_2973))), inference(resolution, [status(thm)], [c_4, c_95328])).
% 59.70/48.21  tff(c_95356, plain, (~v1_xboole_0('#skF_8') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_60, c_95344])).
% 59.70/48.21  tff(c_95367, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_95356])).
% 59.70/48.21  tff(c_26, plain, (![A_15, B_16]: (m1_subset_1(A_15, B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 59.70/48.21  tff(c_99043, plain, (![A_3261, B_3262, C_3263]: (m1_subset_1('#skF_4'(A_3261, B_3262, C_3263), B_3262) | r1_lattice3(A_3261, B_3262, C_3263) | ~m1_subset_1(C_3263, u1_struct_0(A_3261)) | ~l1_orders_2(A_3261))), inference(resolution, [status(thm)], [c_97010, c_26])).
% 59.70/48.21  tff(c_99210, plain, (![A_3270, C_3271]: (m1_subset_1('#skF_4'(A_3270, '#skF_7', C_3271), '#skF_8') | r1_lattice3(A_3270, '#skF_7', C_3271) | ~m1_subset_1(C_3271, u1_struct_0(A_3270)) | ~l1_orders_2(A_3270))), inference(resolution, [status(thm)], [c_99043, c_96726])).
% 59.70/48.21  tff(c_40, plain, (![A_29, B_30]: (k6_domain_1(A_29, B_30)=k1_tarski(B_30) | ~m1_subset_1(B_30, A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_91])).
% 59.70/48.21  tff(c_99215, plain, (![A_3270, C_3271]: (k6_domain_1('#skF_8', '#skF_4'(A_3270, '#skF_7', C_3271))=k1_tarski('#skF_4'(A_3270, '#skF_7', C_3271)) | v1_xboole_0('#skF_8') | r1_lattice3(A_3270, '#skF_7', C_3271) | ~m1_subset_1(C_3271, u1_struct_0(A_3270)) | ~l1_orders_2(A_3270))), inference(resolution, [status(thm)], [c_99210, c_40])).
% 59.70/48.21  tff(c_118144, plain, (![A_3956, C_3957]: (k6_domain_1('#skF_8', '#skF_4'(A_3956, '#skF_7', C_3957))=k1_tarski('#skF_4'(A_3956, '#skF_7', C_3957)) | r1_lattice3(A_3956, '#skF_7', C_3957) | ~m1_subset_1(C_3957, u1_struct_0(A_3956)) | ~l1_orders_2(A_3956))), inference(negUnitSimplification, [status(thm)], [c_95367, c_99215])).
% 59.70/48.21  tff(c_118209, plain, (k6_domain_1('#skF_8', '#skF_4'('#skF_6', '#skF_7', '#skF_9'))=k1_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_9')) | r1_lattice3('#skF_6', '#skF_7', '#skF_9') | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_58, c_118144])).
% 59.70/48.21  tff(c_118228, plain, (k6_domain_1('#skF_8', '#skF_4'('#skF_6', '#skF_7', '#skF_9'))=k1_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_9')) | r1_lattice3('#skF_6', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_118209])).
% 59.70/48.21  tff(c_118229, plain, (k6_domain_1('#skF_8', '#skF_4'('#skF_6', '#skF_7', '#skF_9'))=k1_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_98, c_118228])).
% 59.70/48.21  tff(c_95522, plain, (![A_2999, B_3000]: (r1_tarski(k6_domain_1(A_2999, B_3000), A_2999) | ~m1_subset_1(B_3000, A_2999) | v1_xboole_0(A_2999))), inference(resolution, [status(thm)], [c_95502, c_30])).
% 59.70/48.21  tff(c_118269, plain, (r1_tarski(k1_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_9')), '#skF_8') | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7', '#skF_9'), '#skF_8') | v1_xboole_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_118229, c_95522])).
% 59.70/48.21  tff(c_118296, plain, (r1_tarski(k1_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_9')), '#skF_8') | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_95367, c_118269])).
% 59.70/48.21  tff(c_118299, plain, (~m1_subset_1('#skF_4'('#skF_6', '#skF_7', '#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_118296])).
% 59.70/48.21  tff(c_118302, plain, (~r1_tarski('#skF_7', '#skF_7') | r1_lattice3('#skF_6', '#skF_7', '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_113120, c_118299])).
% 59.70/48.21  tff(c_118311, plain, (r1_lattice3('#skF_6', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_10, c_118302])).
% 59.70/48.21  tff(c_118313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_118311])).
% 59.70/48.21  tff(c_118315, plain, (m1_subset_1('#skF_4'('#skF_6', '#skF_7', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_118296])).
% 59.70/48.21  tff(c_48683, plain, (![A_1617, B_1618, C_1619]: (r2_hidden('#skF_4'(A_1617, B_1618, C_1619), B_1618) | r1_lattice3(A_1617, B_1618, C_1619) | ~m1_subset_1(C_1619, u1_struct_0(A_1617)) | ~l1_orders_2(A_1617))), inference(cnfTransformation, [status(thm)], [f_105])).
% 59.70/48.21  tff(c_47595, plain, (![A_1524, C_1525, B_1526]: (m1_subset_1(A_1524, C_1525) | ~m1_subset_1(B_1526, k1_zfmisc_1(C_1525)) | ~r2_hidden(A_1524, B_1526))), inference(cnfTransformation, [status(thm)], [f_70])).
% 59.70/48.21  tff(c_47601, plain, (![A_1524, B_20, A_19]: (m1_subset_1(A_1524, B_20) | ~r2_hidden(A_1524, A_19) | ~r1_tarski(A_19, B_20))), inference(resolution, [status(thm)], [c_32, c_47595])).
% 59.70/48.21  tff(c_66606, plain, (![A_2362, B_2363, C_2364, B_2365]: (m1_subset_1('#skF_4'(A_2362, B_2363, C_2364), B_2365) | ~r1_tarski(B_2363, B_2365) | r1_lattice3(A_2362, B_2363, C_2364) | ~m1_subset_1(C_2364, u1_struct_0(A_2362)) | ~l1_orders_2(A_2362))), inference(resolution, [status(thm)], [c_48683, c_47601])).
% 59.70/48.21  tff(c_47710, plain, (![A_1544, B_1545]: (m1_subset_1(k6_domain_1(A_1544, B_1545), k1_zfmisc_1(A_1544)) | ~m1_subset_1(B_1545, A_1544) | v1_xboole_0(A_1544))), inference(cnfTransformation, [status(thm)], [f_84])).
% 59.70/48.21  tff(c_47764, plain, (![A_1548, B_1549]: (r1_tarski(k6_domain_1(A_1548, B_1549), A_1548) | ~m1_subset_1(B_1549, A_1548) | v1_xboole_0(A_1548))), inference(resolution, [status(thm)], [c_47710, c_30])).
% 59.70/48.21  tff(c_47554, plain, (![A_1514, C_1515, B_1516]: (r1_tarski(A_1514, C_1515) | ~r1_tarski(B_1516, C_1515) | ~r1_tarski(A_1514, B_1516))), inference(cnfTransformation, [status(thm)], [f_43])).
% 59.70/48.21  tff(c_47563, plain, (![A_1514]: (r1_tarski(A_1514, '#skF_8') | ~r1_tarski(A_1514, '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_47554])).
% 59.70/48.21  tff(c_47790, plain, (![B_1549]: (r1_tarski(k6_domain_1('#skF_7', B_1549), '#skF_8') | ~m1_subset_1(B_1549, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_47764, c_47563])).
% 59.70/48.21  tff(c_47808, plain, (v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_47790])).
% 59.70/48.21  tff(c_48109, plain, (![A_1582, B_1583, C_1584]: (r2_hidden('#skF_4'(A_1582, B_1583, C_1584), B_1583) | r1_lattice3(A_1582, B_1583, C_1584) | ~m1_subset_1(C_1584, u1_struct_0(A_1582)) | ~l1_orders_2(A_1582))), inference(cnfTransformation, [status(thm)], [f_105])).
% 59.70/48.21  tff(c_48212, plain, (![B_1591, A_1592, C_1593]: (~v1_xboole_0(B_1591) | r1_lattice3(A_1592, B_1591, C_1593) | ~m1_subset_1(C_1593, u1_struct_0(A_1592)) | ~l1_orders_2(A_1592))), inference(resolution, [status(thm)], [c_48109, c_2])).
% 59.70/48.21  tff(c_48220, plain, (![B_1591]: (~v1_xboole_0(B_1591) | r1_lattice3('#skF_6', B_1591, '#skF_9') | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_48212])).
% 59.70/48.21  tff(c_48226, plain, (![B_1594]: (~v1_xboole_0(B_1594) | r1_lattice3('#skF_6', B_1594, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_48220])).
% 59.70/48.21  tff(c_48229, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_48226, c_98])).
% 59.70/48.21  tff(c_48233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47808, c_48229])).
% 59.70/48.21  tff(c_48235, plain, (~v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_47790])).
% 59.70/48.21  tff(c_47623, plain, (![A_1531, B_1532, A_1533]: (m1_subset_1(A_1531, B_1532) | ~r2_hidden(A_1531, A_1533) | ~r1_tarski(A_1533, B_1532))), inference(resolution, [status(thm)], [c_32, c_47595])).
% 59.70/48.21  tff(c_48745, plain, (![A_1623, B_1624, B_1625]: (m1_subset_1(A_1623, B_1624) | ~r1_tarski(B_1625, B_1624) | v1_xboole_0(B_1625) | ~m1_subset_1(A_1623, B_1625))), inference(resolution, [status(thm)], [c_28, c_47623])).
% 59.70/48.21  tff(c_48763, plain, (![A_1623]: (m1_subset_1(A_1623, '#skF_8') | v1_xboole_0('#skF_7') | ~m1_subset_1(A_1623, '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_48745])).
% 59.70/48.21  tff(c_48776, plain, (![A_1623]: (m1_subset_1(A_1623, '#skF_8') | ~m1_subset_1(A_1623, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_48235, c_48763])).
% 59.70/48.21  tff(c_66738, plain, (![A_2362, B_2363, C_2364]: (m1_subset_1('#skF_4'(A_2362, B_2363, C_2364), '#skF_8') | ~r1_tarski(B_2363, '#skF_7') | r1_lattice3(A_2362, B_2363, C_2364) | ~m1_subset_1(C_2364, u1_struct_0(A_2362)) | ~l1_orders_2(A_2362))), inference(resolution, [status(thm)], [c_66606, c_48776])).
% 59.70/48.21  tff(c_47577, plain, (![C_1518, B_1519, A_1520]: (~v1_xboole_0(C_1518) | ~m1_subset_1(B_1519, k1_zfmisc_1(C_1518)) | ~r2_hidden(A_1520, B_1519))), inference(cnfTransformation, [status(thm)], [f_77])).
% 59.70/48.21  tff(c_47585, plain, (![B_1521, A_1522, A_1523]: (~v1_xboole_0(B_1521) | ~r2_hidden(A_1522, A_1523) | ~r1_tarski(A_1523, B_1521))), inference(resolution, [status(thm)], [c_32, c_47577])).
% 59.70/48.21  tff(c_47609, plain, (![B_1529, A_1530]: (~v1_xboole_0(B_1529) | ~r1_tarski(A_1530, B_1529) | v1_xboole_0(A_1530))), inference(resolution, [status(thm)], [c_4, c_47585])).
% 59.70/48.21  tff(c_47621, plain, (~v1_xboole_0('#skF_8') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_60, c_47609])).
% 59.70/48.21  tff(c_47622, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_47621])).
% 59.70/48.21  tff(c_50548, plain, (![A_1760, B_1761, C_1762]: (m1_subset_1('#skF_4'(A_1760, B_1761, C_1762), B_1761) | r1_lattice3(A_1760, B_1761, C_1762) | ~m1_subset_1(C_1762, u1_struct_0(A_1760)) | ~l1_orders_2(A_1760))), inference(resolution, [status(thm)], [c_48683, c_26])).
% 59.70/48.21  tff(c_50719, plain, (![A_1768, C_1769]: (m1_subset_1('#skF_4'(A_1768, '#skF_7', C_1769), '#skF_8') | r1_lattice3(A_1768, '#skF_7', C_1769) | ~m1_subset_1(C_1769, u1_struct_0(A_1768)) | ~l1_orders_2(A_1768))), inference(resolution, [status(thm)], [c_50548, c_48776])).
% 59.70/48.21  tff(c_50722, plain, (![A_1768, C_1769]: (k6_domain_1('#skF_8', '#skF_4'(A_1768, '#skF_7', C_1769))=k1_tarski('#skF_4'(A_1768, '#skF_7', C_1769)) | v1_xboole_0('#skF_8') | r1_lattice3(A_1768, '#skF_7', C_1769) | ~m1_subset_1(C_1769, u1_struct_0(A_1768)) | ~l1_orders_2(A_1768))), inference(resolution, [status(thm)], [c_50719, c_40])).
% 59.70/48.21  tff(c_68238, plain, (![A_2431, C_2432]: (k6_domain_1('#skF_8', '#skF_4'(A_2431, '#skF_7', C_2432))=k1_tarski('#skF_4'(A_2431, '#skF_7', C_2432)) | r1_lattice3(A_2431, '#skF_7', C_2432) | ~m1_subset_1(C_2432, u1_struct_0(A_2431)) | ~l1_orders_2(A_2431))), inference(negUnitSimplification, [status(thm)], [c_47622, c_50722])).
% 59.70/48.21  tff(c_68303, plain, (k6_domain_1('#skF_8', '#skF_4'('#skF_6', '#skF_7', '#skF_9'))=k1_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_9')) | r1_lattice3('#skF_6', '#skF_7', '#skF_9') | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_58, c_68238])).
% 59.70/48.21  tff(c_68322, plain, (k6_domain_1('#skF_8', '#skF_4'('#skF_6', '#skF_7', '#skF_9'))=k1_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_9')) | r1_lattice3('#skF_6', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_68303])).
% 59.70/48.21  tff(c_68323, plain, (k6_domain_1('#skF_8', '#skF_4'('#skF_6', '#skF_7', '#skF_9'))=k1_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_98, c_68322])).
% 59.70/48.21  tff(c_47727, plain, (![A_1544, B_1545]: (r1_tarski(k6_domain_1(A_1544, B_1545), A_1544) | ~m1_subset_1(B_1545, A_1544) | v1_xboole_0(A_1544))), inference(resolution, [status(thm)], [c_47710, c_30])).
% 59.70/48.21  tff(c_68368, plain, (r1_tarski(k1_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_9')), '#skF_8') | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7', '#skF_9'), '#skF_8') | v1_xboole_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_68323, c_47727])).
% 59.70/48.21  tff(c_68395, plain, (r1_tarski(k1_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_9')), '#skF_8') | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_47622, c_68368])).
% 59.70/48.21  tff(c_68398, plain, (~m1_subset_1('#skF_4'('#skF_6', '#skF_7', '#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_68395])).
% 59.70/48.21  tff(c_68401, plain, (~r1_tarski('#skF_7', '#skF_7') | r1_lattice3('#skF_6', '#skF_7', '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_66738, c_68398])).
% 59.70/48.21  tff(c_68410, plain, (r1_lattice3('#skF_6', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_10, c_68401])).
% 59.70/48.21  tff(c_68412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_68410])).
% 59.70/48.21  tff(c_68414, plain, (m1_subset_1('#skF_4'('#skF_6', '#skF_7', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_68395])).
% 59.70/48.21  tff(c_66, plain, (r1_lattice3('#skF_6', '#skF_8', '#skF_9') | ~r2_lattice3('#skF_6', '#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_136])).
% 59.70/48.21  tff(c_151, plain, (~r2_lattice3('#skF_6', '#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_66])).
% 59.70/48.21  tff(c_1375, plain, (![A_190, B_191, C_192]: (r2_hidden('#skF_5'(A_190, B_191, C_192), B_191) | r2_lattice3(A_190, B_191, C_192) | ~m1_subset_1(C_192, u1_struct_0(A_190)) | ~l1_orders_2(A_190))), inference(cnfTransformation, [status(thm)], [f_119])).
% 59.70/48.21  tff(c_233, plain, (![A_96, C_97, B_98]: (m1_subset_1(A_96, C_97) | ~m1_subset_1(B_98, k1_zfmisc_1(C_97)) | ~r2_hidden(A_96, B_98))), inference(cnfTransformation, [status(thm)], [f_70])).
% 59.70/48.21  tff(c_239, plain, (![A_96, B_20, A_19]: (m1_subset_1(A_96, B_20) | ~r2_hidden(A_96, A_19) | ~r1_tarski(A_19, B_20))), inference(resolution, [status(thm)], [c_32, c_233])).
% 59.70/48.21  tff(c_16976, plain, (![A_885, B_886, C_887, B_888]: (m1_subset_1('#skF_5'(A_885, B_886, C_887), B_888) | ~r1_tarski(B_886, B_888) | r2_lattice3(A_885, B_886, C_887) | ~m1_subset_1(C_887, u1_struct_0(A_885)) | ~l1_orders_2(A_885))), inference(resolution, [status(thm)], [c_1375, c_239])).
% 59.70/48.21  tff(c_344, plain, (![A_115, B_116]: (m1_subset_1(k6_domain_1(A_115, B_116), k1_zfmisc_1(A_115)) | ~m1_subset_1(B_116, A_115) | v1_xboole_0(A_115))), inference(cnfTransformation, [status(thm)], [f_84])).
% 59.70/48.21  tff(c_397, plain, (![A_120, B_121]: (r1_tarski(k6_domain_1(A_120, B_121), A_120) | ~m1_subset_1(B_121, A_120) | v1_xboole_0(A_120))), inference(resolution, [status(thm)], [c_344, c_30])).
% 59.70/48.21  tff(c_186, plain, (![A_84, C_85, B_86]: (r1_tarski(A_84, C_85) | ~r1_tarski(B_86, C_85) | ~r1_tarski(A_84, B_86))), inference(cnfTransformation, [status(thm)], [f_43])).
% 59.70/48.21  tff(c_195, plain, (![A_84]: (r1_tarski(A_84, '#skF_8') | ~r1_tarski(A_84, '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_186])).
% 59.70/48.21  tff(c_423, plain, (![B_121]: (r1_tarski(k6_domain_1('#skF_7', B_121), '#skF_8') | ~m1_subset_1(B_121, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_397, c_195])).
% 59.70/48.21  tff(c_446, plain, (v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_423])).
% 59.70/48.21  tff(c_781, plain, (![A_154, B_155, C_156]: (r2_hidden('#skF_5'(A_154, B_155, C_156), B_155) | r2_lattice3(A_154, B_155, C_156) | ~m1_subset_1(C_156, u1_struct_0(A_154)) | ~l1_orders_2(A_154))), inference(cnfTransformation, [status(thm)], [f_119])).
% 59.70/48.21  tff(c_844, plain, (![B_161, A_162, C_163]: (~v1_xboole_0(B_161) | r2_lattice3(A_162, B_161, C_163) | ~m1_subset_1(C_163, u1_struct_0(A_162)) | ~l1_orders_2(A_162))), inference(resolution, [status(thm)], [c_781, c_2])).
% 59.70/48.21  tff(c_852, plain, (![B_161]: (~v1_xboole_0(B_161) | r2_lattice3('#skF_6', B_161, '#skF_9') | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_844])).
% 59.70/48.21  tff(c_858, plain, (![B_164]: (~v1_xboole_0(B_164) | r2_lattice3('#skF_6', B_164, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_852])).
% 59.70/48.21  tff(c_861, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_858, c_151])).
% 59.70/48.21  tff(c_865, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_446, c_861])).
% 59.70/48.21  tff(c_867, plain, (~v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_423])).
% 59.70/48.21  tff(c_283, plain, (![A_104, B_105, A_106]: (m1_subset_1(A_104, B_105) | ~r2_hidden(A_104, A_106) | ~r1_tarski(A_106, B_105))), inference(resolution, [status(thm)], [c_32, c_233])).
% 59.70/48.21  tff(c_1463, plain, (![A_199, B_200, B_201]: (m1_subset_1(A_199, B_200) | ~r1_tarski(B_201, B_200) | v1_xboole_0(B_201) | ~m1_subset_1(A_199, B_201))), inference(resolution, [status(thm)], [c_28, c_283])).
% 59.70/48.21  tff(c_1481, plain, (![A_199]: (m1_subset_1(A_199, '#skF_8') | v1_xboole_0('#skF_7') | ~m1_subset_1(A_199, '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_1463])).
% 59.70/48.21  tff(c_1494, plain, (![A_199]: (m1_subset_1(A_199, '#skF_8') | ~m1_subset_1(A_199, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_867, c_1481])).
% 59.70/48.21  tff(c_17104, plain, (![A_885, B_886, C_887]: (m1_subset_1('#skF_5'(A_885, B_886, C_887), '#skF_8') | ~r1_tarski(B_886, '#skF_7') | r2_lattice3(A_885, B_886, C_887) | ~m1_subset_1(C_887, u1_struct_0(A_885)) | ~l1_orders_2(A_885))), inference(resolution, [status(thm)], [c_16976, c_1494])).
% 59.70/48.21  tff(c_209, plain, (![C_88, B_89, A_90]: (~v1_xboole_0(C_88) | ~m1_subset_1(B_89, k1_zfmisc_1(C_88)) | ~r2_hidden(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_77])).
% 59.70/48.21  tff(c_217, plain, (![B_91, A_92, A_93]: (~v1_xboole_0(B_91) | ~r2_hidden(A_92, A_93) | ~r1_tarski(A_93, B_91))), inference(resolution, [status(thm)], [c_32, c_209])).
% 59.70/48.21  tff(c_241, plain, (![B_99, A_100]: (~v1_xboole_0(B_99) | ~r1_tarski(A_100, B_99) | v1_xboole_0(A_100))), inference(resolution, [status(thm)], [c_4, c_217])).
% 59.70/48.21  tff(c_253, plain, (~v1_xboole_0('#skF_8') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_60, c_241])).
% 59.70/48.21  tff(c_254, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_253])).
% 59.70/48.21  tff(c_3281, plain, (![A_329, B_330, C_331]: (m1_subset_1('#skF_5'(A_329, B_330, C_331), B_330) | r2_lattice3(A_329, B_330, C_331) | ~m1_subset_1(C_331, u1_struct_0(A_329)) | ~l1_orders_2(A_329))), inference(resolution, [status(thm)], [c_1375, c_26])).
% 59.70/48.21  tff(c_3334, plain, (![A_334, C_335]: (m1_subset_1('#skF_5'(A_334, '#skF_7', C_335), '#skF_8') | r2_lattice3(A_334, '#skF_7', C_335) | ~m1_subset_1(C_335, u1_struct_0(A_334)) | ~l1_orders_2(A_334))), inference(resolution, [status(thm)], [c_3281, c_1494])).
% 59.70/48.21  tff(c_3337, plain, (![A_334, C_335]: (k6_domain_1('#skF_8', '#skF_5'(A_334, '#skF_7', C_335))=k1_tarski('#skF_5'(A_334, '#skF_7', C_335)) | v1_xboole_0('#skF_8') | r2_lattice3(A_334, '#skF_7', C_335) | ~m1_subset_1(C_335, u1_struct_0(A_334)) | ~l1_orders_2(A_334))), inference(resolution, [status(thm)], [c_3334, c_40])).
% 59.70/48.21  tff(c_20504, plain, (![A_975, C_976]: (k6_domain_1('#skF_8', '#skF_5'(A_975, '#skF_7', C_976))=k1_tarski('#skF_5'(A_975, '#skF_7', C_976)) | r2_lattice3(A_975, '#skF_7', C_976) | ~m1_subset_1(C_976, u1_struct_0(A_975)) | ~l1_orders_2(A_975))), inference(negUnitSimplification, [status(thm)], [c_254, c_3337])).
% 59.70/48.21  tff(c_20569, plain, (k6_domain_1('#skF_8', '#skF_5'('#skF_6', '#skF_7', '#skF_9'))=k1_tarski('#skF_5'('#skF_6', '#skF_7', '#skF_9')) | r2_lattice3('#skF_6', '#skF_7', '#skF_9') | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_58, c_20504])).
% 59.70/48.21  tff(c_20588, plain, (k6_domain_1('#skF_8', '#skF_5'('#skF_6', '#skF_7', '#skF_9'))=k1_tarski('#skF_5'('#skF_6', '#skF_7', '#skF_9')) | r2_lattice3('#skF_6', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_20569])).
% 59.70/48.21  tff(c_20589, plain, (k6_domain_1('#skF_8', '#skF_5'('#skF_6', '#skF_7', '#skF_9'))=k1_tarski('#skF_5'('#skF_6', '#skF_7', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_151, c_20588])).
% 59.70/48.21  tff(c_364, plain, (![A_115, B_116]: (r1_tarski(k6_domain_1(A_115, B_116), A_115) | ~m1_subset_1(B_116, A_115) | v1_xboole_0(A_115))), inference(resolution, [status(thm)], [c_344, c_30])).
% 59.70/48.21  tff(c_20629, plain, (r1_tarski(k1_tarski('#skF_5'('#skF_6', '#skF_7', '#skF_9')), '#skF_8') | ~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_9'), '#skF_8') | v1_xboole_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_20589, c_364])).
% 59.70/48.21  tff(c_20656, plain, (r1_tarski(k1_tarski('#skF_5'('#skF_6', '#skF_7', '#skF_9')), '#skF_8') | ~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_254, c_20629])).
% 59.70/48.21  tff(c_20659, plain, (~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_20656])).
% 59.70/48.21  tff(c_20662, plain, (~r1_tarski('#skF_7', '#skF_7') | r2_lattice3('#skF_6', '#skF_7', '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_17104, c_20659])).
% 59.70/48.21  tff(c_20671, plain, (r2_lattice3('#skF_6', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_10, c_20662])).
% 59.70/48.21  tff(c_20673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_20671])).
% 59.70/48.21  tff(c_20675, plain, (m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_20656])).
% 59.70/48.21  tff(c_70, plain, (r1_lattice3('#skF_6', '#skF_8', '#skF_9') | r2_lattice3('#skF_6', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_136])).
% 59.70/48.21  tff(c_152, plain, (r2_lattice3('#skF_6', '#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_70])).
% 59.70/48.21  tff(c_56, plain, (![A_43, B_50, C_51]: (m1_subset_1('#skF_5'(A_43, B_50, C_51), u1_struct_0(A_43)) | r2_lattice3(A_43, B_50, C_51) | ~m1_subset_1(C_51, u1_struct_0(A_43)) | ~l1_orders_2(A_43))), inference(cnfTransformation, [status(thm)], [f_119])).
% 59.70/48.21  tff(c_2614, plain, (![A_293, D_294, C_295, B_296]: (r1_orders_2(A_293, D_294, C_295) | ~r2_hidden(D_294, B_296) | ~m1_subset_1(D_294, u1_struct_0(A_293)) | ~r2_lattice3(A_293, B_296, C_295) | ~m1_subset_1(C_295, u1_struct_0(A_293)) | ~l1_orders_2(A_293))), inference(cnfTransformation, [status(thm)], [f_119])).
% 59.70/48.21  tff(c_6063, plain, (![A_460, A_461, C_462, B_463]: (r1_orders_2(A_460, A_461, C_462) | ~m1_subset_1(A_461, u1_struct_0(A_460)) | ~r2_lattice3(A_460, B_463, C_462) | ~m1_subset_1(C_462, u1_struct_0(A_460)) | ~l1_orders_2(A_460) | v1_xboole_0(B_463) | ~m1_subset_1(A_461, B_463))), inference(resolution, [status(thm)], [c_28, c_2614])).
% 59.70/48.21  tff(c_46382, plain, (![C_1423, B_1425, A_1424, C_1421, B_1422]: (r1_orders_2(A_1424, '#skF_5'(A_1424, B_1422, C_1421), C_1423) | ~r2_lattice3(A_1424, B_1425, C_1423) | ~m1_subset_1(C_1423, u1_struct_0(A_1424)) | v1_xboole_0(B_1425) | ~m1_subset_1('#skF_5'(A_1424, B_1422, C_1421), B_1425) | r2_lattice3(A_1424, B_1422, C_1421) | ~m1_subset_1(C_1421, u1_struct_0(A_1424)) | ~l1_orders_2(A_1424))), inference(resolution, [status(thm)], [c_56, c_6063])).
% 59.70/48.21  tff(c_46404, plain, (![B_1422, C_1421]: (r1_orders_2('#skF_6', '#skF_5'('#skF_6', B_1422, C_1421), '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | v1_xboole_0('#skF_8') | ~m1_subset_1('#skF_5'('#skF_6', B_1422, C_1421), '#skF_8') | r2_lattice3('#skF_6', B_1422, C_1421) | ~m1_subset_1(C_1421, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_152, c_46382])).
% 59.70/48.21  tff(c_46421, plain, (![B_1422, C_1421]: (r1_orders_2('#skF_6', '#skF_5'('#skF_6', B_1422, C_1421), '#skF_9') | v1_xboole_0('#skF_8') | ~m1_subset_1('#skF_5'('#skF_6', B_1422, C_1421), '#skF_8') | r2_lattice3('#skF_6', B_1422, C_1421) | ~m1_subset_1(C_1421, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_46404])).
% 59.70/48.21  tff(c_46626, plain, (![B_1430, C_1431]: (r1_orders_2('#skF_6', '#skF_5'('#skF_6', B_1430, C_1431), '#skF_9') | ~m1_subset_1('#skF_5'('#skF_6', B_1430, C_1431), '#skF_8') | r2_lattice3('#skF_6', B_1430, C_1431) | ~m1_subset_1(C_1431, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_254, c_46421])).
% 59.70/48.21  tff(c_52, plain, (![A_43, B_50, C_51]: (~r1_orders_2(A_43, '#skF_5'(A_43, B_50, C_51), C_51) | r2_lattice3(A_43, B_50, C_51) | ~m1_subset_1(C_51, u1_struct_0(A_43)) | ~l1_orders_2(A_43))), inference(cnfTransformation, [status(thm)], [f_119])).
% 59.70/48.21  tff(c_46630, plain, (![B_1430]: (~l1_orders_2('#skF_6') | ~m1_subset_1('#skF_5'('#skF_6', B_1430, '#skF_9'), '#skF_8') | r2_lattice3('#skF_6', B_1430, '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_46626, c_52])).
% 59.70/48.21  tff(c_46644, plain, (![B_1432]: (~m1_subset_1('#skF_5'('#skF_6', B_1432, '#skF_9'), '#skF_8') | r2_lattice3('#skF_6', B_1432, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_46630])).
% 59.70/48.21  tff(c_46666, plain, (r2_lattice3('#skF_6', '#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_20675, c_46644])).
% 59.70/48.21  tff(c_46701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_46666])).
% 59.70/48.21  tff(c_46702, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_253])).
% 59.70/48.21  tff(c_47200, plain, (![A_1478, B_1479, C_1480]: (r2_hidden('#skF_4'(A_1478, B_1479, C_1480), B_1479) | r1_lattice3(A_1478, B_1479, C_1480) | ~m1_subset_1(C_1480, u1_struct_0(A_1478)) | ~l1_orders_2(A_1478))), inference(cnfTransformation, [status(thm)], [f_105])).
% 59.70/48.21  tff(c_47497, plain, (![B_1505, A_1506, C_1507]: (~v1_xboole_0(B_1505) | r1_lattice3(A_1506, B_1505, C_1507) | ~m1_subset_1(C_1507, u1_struct_0(A_1506)) | ~l1_orders_2(A_1506))), inference(resolution, [status(thm)], [c_47200, c_2])).
% 59.70/48.21  tff(c_47505, plain, (![B_1505]: (~v1_xboole_0(B_1505) | r1_lattice3('#skF_6', B_1505, '#skF_9') | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_47497])).
% 59.70/48.21  tff(c_47511, plain, (![B_1508]: (~v1_xboole_0(B_1508) | r1_lattice3('#skF_6', B_1508, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_47505])).
% 59.70/48.21  tff(c_47514, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_47511, c_98])).
% 59.70/48.21  tff(c_47518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46702, c_47514])).
% 59.70/48.21  tff(c_47519, plain, (r1_lattice3('#skF_6', '#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_70])).
% 59.70/48.21  tff(c_48, plain, (![A_31, B_38, C_39]: (m1_subset_1('#skF_4'(A_31, B_38, C_39), u1_struct_0(A_31)) | r1_lattice3(A_31, B_38, C_39) | ~m1_subset_1(C_39, u1_struct_0(A_31)) | ~l1_orders_2(A_31))), inference(cnfTransformation, [status(thm)], [f_105])).
% 59.70/48.21  tff(c_49937, plain, (![A_1724, C_1725, D_1726, B_1727]: (r1_orders_2(A_1724, C_1725, D_1726) | ~r2_hidden(D_1726, B_1727) | ~m1_subset_1(D_1726, u1_struct_0(A_1724)) | ~r1_lattice3(A_1724, B_1727, C_1725) | ~m1_subset_1(C_1725, u1_struct_0(A_1724)) | ~l1_orders_2(A_1724))), inference(cnfTransformation, [status(thm)], [f_105])).
% 59.70/48.21  tff(c_53704, plain, (![A_1915, C_1916, A_1917, B_1918]: (r1_orders_2(A_1915, C_1916, A_1917) | ~m1_subset_1(A_1917, u1_struct_0(A_1915)) | ~r1_lattice3(A_1915, B_1918, C_1916) | ~m1_subset_1(C_1916, u1_struct_0(A_1915)) | ~l1_orders_2(A_1915) | v1_xboole_0(B_1918) | ~m1_subset_1(A_1917, B_1918))), inference(resolution, [status(thm)], [c_28, c_49937])).
% 59.70/48.21  tff(c_94191, plain, (![C_2878, B_2875, C_2874, B_2876, A_2877]: (r1_orders_2(A_2877, C_2874, '#skF_4'(A_2877, B_2876, C_2878)) | ~r1_lattice3(A_2877, B_2875, C_2874) | ~m1_subset_1(C_2874, u1_struct_0(A_2877)) | v1_xboole_0(B_2875) | ~m1_subset_1('#skF_4'(A_2877, B_2876, C_2878), B_2875) | r1_lattice3(A_2877, B_2876, C_2878) | ~m1_subset_1(C_2878, u1_struct_0(A_2877)) | ~l1_orders_2(A_2877))), inference(resolution, [status(thm)], [c_48, c_53704])).
% 59.70/48.21  tff(c_94213, plain, (![B_2876, C_2878]: (r1_orders_2('#skF_6', '#skF_9', '#skF_4'('#skF_6', B_2876, C_2878)) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | v1_xboole_0('#skF_8') | ~m1_subset_1('#skF_4'('#skF_6', B_2876, C_2878), '#skF_8') | r1_lattice3('#skF_6', B_2876, C_2878) | ~m1_subset_1(C_2878, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_47519, c_94191])).
% 59.70/48.21  tff(c_94230, plain, (![B_2876, C_2878]: (r1_orders_2('#skF_6', '#skF_9', '#skF_4'('#skF_6', B_2876, C_2878)) | v1_xboole_0('#skF_8') | ~m1_subset_1('#skF_4'('#skF_6', B_2876, C_2878), '#skF_8') | r1_lattice3('#skF_6', B_2876, C_2878) | ~m1_subset_1(C_2878, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_94213])).
% 59.70/48.21  tff(c_94410, plain, (![B_2882, C_2883]: (r1_orders_2('#skF_6', '#skF_9', '#skF_4'('#skF_6', B_2882, C_2883)) | ~m1_subset_1('#skF_4'('#skF_6', B_2882, C_2883), '#skF_8') | r1_lattice3('#skF_6', B_2882, C_2883) | ~m1_subset_1(C_2883, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_47622, c_94230])).
% 59.70/48.21  tff(c_44, plain, (![A_31, C_39, B_38]: (~r1_orders_2(A_31, C_39, '#skF_4'(A_31, B_38, C_39)) | r1_lattice3(A_31, B_38, C_39) | ~m1_subset_1(C_39, u1_struct_0(A_31)) | ~l1_orders_2(A_31))), inference(cnfTransformation, [status(thm)], [f_105])).
% 59.70/48.21  tff(c_94414, plain, (![B_2882]: (~l1_orders_2('#skF_6') | ~m1_subset_1('#skF_4'('#skF_6', B_2882, '#skF_9'), '#skF_8') | r1_lattice3('#skF_6', B_2882, '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_94410, c_44])).
% 59.70/48.21  tff(c_94428, plain, (![B_2884]: (~m1_subset_1('#skF_4'('#skF_6', B_2884, '#skF_9'), '#skF_8') | r1_lattice3('#skF_6', B_2884, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_94414])).
% 59.70/48.21  tff(c_94450, plain, (r1_lattice3('#skF_6', '#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_68414, c_94428])).
% 59.70/48.21  tff(c_94485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_94450])).
% 59.70/48.21  tff(c_94486, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_47621])).
% 59.70/48.21  tff(c_94984, plain, (![A_2930, B_2931, C_2932]: (r2_hidden('#skF_4'(A_2930, B_2931, C_2932), B_2931) | r1_lattice3(A_2930, B_2931, C_2932) | ~m1_subset_1(C_2932, u1_struct_0(A_2930)) | ~l1_orders_2(A_2930))), inference(cnfTransformation, [status(thm)], [f_105])).
% 59.70/48.21  tff(c_95257, plain, (![B_2955, A_2956, C_2957]: (~v1_xboole_0(B_2955) | r1_lattice3(A_2956, B_2955, C_2957) | ~m1_subset_1(C_2957, u1_struct_0(A_2956)) | ~l1_orders_2(A_2956))), inference(resolution, [status(thm)], [c_94984, c_2])).
% 59.70/48.21  tff(c_95267, plain, (![B_2955]: (~v1_xboole_0(B_2955) | r1_lattice3('#skF_6', B_2955, '#skF_9') | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_95257])).
% 59.70/48.21  tff(c_95274, plain, (![B_2958]: (~v1_xboole_0(B_2958) | r1_lattice3('#skF_6', B_2958, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_95267])).
% 59.70/48.21  tff(c_95277, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_95274, c_98])).
% 59.70/48.21  tff(c_95281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94486, c_95277])).
% 59.70/48.21  tff(c_95282, plain, (r1_lattice3('#skF_6', '#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_66])).
% 59.70/48.21  tff(c_98322, plain, (![A_3219, C_3220, D_3221, B_3222]: (r1_orders_2(A_3219, C_3220, D_3221) | ~r2_hidden(D_3221, B_3222) | ~m1_subset_1(D_3221, u1_struct_0(A_3219)) | ~r1_lattice3(A_3219, B_3222, C_3220) | ~m1_subset_1(C_3220, u1_struct_0(A_3219)) | ~l1_orders_2(A_3219))), inference(cnfTransformation, [status(thm)], [f_105])).
% 59.70/48.21  tff(c_101748, plain, (![A_3397, C_3398, A_3399, B_3400]: (r1_orders_2(A_3397, C_3398, A_3399) | ~m1_subset_1(A_3399, u1_struct_0(A_3397)) | ~r1_lattice3(A_3397, B_3400, C_3398) | ~m1_subset_1(C_3398, u1_struct_0(A_3397)) | ~l1_orders_2(A_3397) | v1_xboole_0(B_3400) | ~m1_subset_1(A_3399, B_3400))), inference(resolution, [status(thm)], [c_28, c_98322])).
% 59.70/48.21  tff(c_148104, plain, (![B_4442, C_4444, C_4445, A_4443, B_4441]: (r1_orders_2(A_4443, C_4445, '#skF_4'(A_4443, B_4442, C_4444)) | ~r1_lattice3(A_4443, B_4441, C_4445) | ~m1_subset_1(C_4445, u1_struct_0(A_4443)) | v1_xboole_0(B_4441) | ~m1_subset_1('#skF_4'(A_4443, B_4442, C_4444), B_4441) | r1_lattice3(A_4443, B_4442, C_4444) | ~m1_subset_1(C_4444, u1_struct_0(A_4443)) | ~l1_orders_2(A_4443))), inference(resolution, [status(thm)], [c_48, c_101748])).
% 59.70/48.21  tff(c_148126, plain, (![B_4442, C_4444]: (r1_orders_2('#skF_6', '#skF_9', '#skF_4'('#skF_6', B_4442, C_4444)) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | v1_xboole_0('#skF_8') | ~m1_subset_1('#skF_4'('#skF_6', B_4442, C_4444), '#skF_8') | r1_lattice3('#skF_6', B_4442, C_4444) | ~m1_subset_1(C_4444, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_95282, c_148104])).
% 59.70/48.21  tff(c_148143, plain, (![B_4442, C_4444]: (r1_orders_2('#skF_6', '#skF_9', '#skF_4'('#skF_6', B_4442, C_4444)) | v1_xboole_0('#skF_8') | ~m1_subset_1('#skF_4'('#skF_6', B_4442, C_4444), '#skF_8') | r1_lattice3('#skF_6', B_4442, C_4444) | ~m1_subset_1(C_4444, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_148126])).
% 59.70/48.21  tff(c_148361, plain, (![B_4449, C_4450]: (r1_orders_2('#skF_6', '#skF_9', '#skF_4'('#skF_6', B_4449, C_4450)) | ~m1_subset_1('#skF_4'('#skF_6', B_4449, C_4450), '#skF_8') | r1_lattice3('#skF_6', B_4449, C_4450) | ~m1_subset_1(C_4450, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_95367, c_148143])).
% 59.70/48.21  tff(c_148365, plain, (![B_4449]: (~l1_orders_2('#skF_6') | ~m1_subset_1('#skF_4'('#skF_6', B_4449, '#skF_9'), '#skF_8') | r1_lattice3('#skF_6', B_4449, '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_148361, c_44])).
% 59.70/48.21  tff(c_148379, plain, (![B_4451]: (~m1_subset_1('#skF_4'('#skF_6', B_4451, '#skF_9'), '#skF_8') | r1_lattice3('#skF_6', B_4451, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_148365])).
% 59.70/48.21  tff(c_148398, plain, (r1_lattice3('#skF_6', '#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_118315, c_148379])).
% 59.70/48.21  tff(c_148436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_148398])).
% 59.70/48.21  tff(c_148437, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_95356])).
% 59.70/48.21  tff(c_149105, plain, (![A_4516, B_4517, C_4518]: (r2_hidden('#skF_4'(A_4516, B_4517, C_4518), B_4517) | r1_lattice3(A_4516, B_4517, C_4518) | ~m1_subset_1(C_4518, u1_struct_0(A_4516)) | ~l1_orders_2(A_4516))), inference(cnfTransformation, [status(thm)], [f_105])).
% 59.70/48.21  tff(c_149309, plain, (![B_4534, A_4535, C_4536]: (~v1_xboole_0(B_4534) | r1_lattice3(A_4535, B_4534, C_4536) | ~m1_subset_1(C_4536, u1_struct_0(A_4535)) | ~l1_orders_2(A_4535))), inference(resolution, [status(thm)], [c_149105, c_2])).
% 59.70/48.21  tff(c_149322, plain, (![B_4534]: (~v1_xboole_0(B_4534) | r1_lattice3('#skF_6', B_4534, '#skF_9') | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_149309])).
% 59.70/48.21  tff(c_149330, plain, (![B_4537]: (~v1_xboole_0(B_4537) | r1_lattice3('#skF_6', B_4537, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_149322])).
% 59.70/48.21  tff(c_149333, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_149330, c_98])).
% 59.70/48.21  tff(c_149337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148437, c_149333])).
% 59.70/48.21  tff(c_149339, plain, (r1_lattice3('#skF_6', '#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_68])).
% 59.70/48.21  tff(c_64, plain, (~r1_lattice3('#skF_6', '#skF_7', '#skF_9') | ~r2_lattice3('#skF_6', '#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_136])).
% 59.70/48.21  tff(c_149383, plain, (~r2_lattice3('#skF_6', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_149339, c_64])).
% 59.70/48.21  tff(c_151010, plain, (![A_4692, B_4693, C_4694]: (r2_hidden('#skF_5'(A_4692, B_4693, C_4694), B_4693) | r2_lattice3(A_4692, B_4693, C_4694) | ~m1_subset_1(C_4694, u1_struct_0(A_4692)) | ~l1_orders_2(A_4692))), inference(cnfTransformation, [status(thm)], [f_119])).
% 59.70/48.21  tff(c_149469, plain, (![A_4564, C_4565, B_4566]: (m1_subset_1(A_4564, C_4565) | ~m1_subset_1(B_4566, k1_zfmisc_1(C_4565)) | ~r2_hidden(A_4564, B_4566))), inference(cnfTransformation, [status(thm)], [f_70])).
% 59.70/48.21  tff(c_149475, plain, (![A_4564, B_20, A_19]: (m1_subset_1(A_4564, B_20) | ~r2_hidden(A_4564, A_19) | ~r1_tarski(A_19, B_20))), inference(resolution, [status(thm)], [c_32, c_149469])).
% 59.70/48.21  tff(c_168366, plain, (![A_5417, B_5418, C_5419, B_5420]: (m1_subset_1('#skF_5'(A_5417, B_5418, C_5419), B_5420) | ~r1_tarski(B_5418, B_5420) | r2_lattice3(A_5417, B_5418, C_5419) | ~m1_subset_1(C_5419, u1_struct_0(A_5417)) | ~l1_orders_2(A_5417))), inference(resolution, [status(thm)], [c_151010, c_149475])).
% 59.70/48.21  tff(c_149584, plain, (![A_4584, B_4585]: (m1_subset_1(k6_domain_1(A_4584, B_4585), k1_zfmisc_1(A_4584)) | ~m1_subset_1(B_4585, A_4584) | v1_xboole_0(A_4584))), inference(cnfTransformation, [status(thm)], [f_84])).
% 59.70/48.21  tff(c_149638, plain, (![A_4588, B_4589]: (r1_tarski(k6_domain_1(A_4588, B_4589), A_4588) | ~m1_subset_1(B_4589, A_4588) | v1_xboole_0(A_4588))), inference(resolution, [status(thm)], [c_149584, c_30])).
% 59.70/48.21  tff(c_149428, plain, (![A_4554, C_4555, B_4556]: (r1_tarski(A_4554, C_4555) | ~r1_tarski(B_4556, C_4555) | ~r1_tarski(A_4554, B_4556))), inference(cnfTransformation, [status(thm)], [f_43])).
% 59.70/48.21  tff(c_149437, plain, (![A_4554]: (r1_tarski(A_4554, '#skF_8') | ~r1_tarski(A_4554, '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_149428])).
% 59.70/48.21  tff(c_149664, plain, (![B_4589]: (r1_tarski(k6_domain_1('#skF_7', B_4589), '#skF_8') | ~m1_subset_1(B_4589, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_149638, c_149437])).
% 59.70/48.21  tff(c_149682, plain, (v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_149664])).
% 59.70/48.21  tff(c_150129, plain, (![A_4637, B_4638, C_4639]: (r2_hidden('#skF_5'(A_4637, B_4638, C_4639), B_4638) | r2_lattice3(A_4637, B_4638, C_4639) | ~m1_subset_1(C_4639, u1_struct_0(A_4637)) | ~l1_orders_2(A_4637))), inference(cnfTransformation, [status(thm)], [f_119])).
% 59.70/48.21  tff(c_150191, plain, (![B_4642, A_4643, C_4644]: (~v1_xboole_0(B_4642) | r2_lattice3(A_4643, B_4642, C_4644) | ~m1_subset_1(C_4644, u1_struct_0(A_4643)) | ~l1_orders_2(A_4643))), inference(resolution, [status(thm)], [c_150129, c_2])).
% 59.70/48.21  tff(c_150202, plain, (![B_4642]: (~v1_xboole_0(B_4642) | r2_lattice3('#skF_6', B_4642, '#skF_9') | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_150191])).
% 59.70/48.21  tff(c_150209, plain, (![B_4645]: (~v1_xboole_0(B_4645) | r2_lattice3('#skF_6', B_4645, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_150202])).
% 59.70/48.21  tff(c_150212, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_150209, c_149383])).
% 59.70/48.21  tff(c_150216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149682, c_150212])).
% 59.70/48.21  tff(c_150218, plain, (~v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_149664])).
% 59.70/48.21  tff(c_149497, plain, (![A_4571, B_4572, A_4573]: (m1_subset_1(A_4571, B_4572) | ~r2_hidden(A_4571, A_4573) | ~r1_tarski(A_4573, B_4572))), inference(resolution, [status(thm)], [c_32, c_149469])).
% 59.70/48.21  tff(c_150700, plain, (![A_4671, B_4672, B_4673]: (m1_subset_1(A_4671, B_4672) | ~r1_tarski(B_4673, B_4672) | v1_xboole_0(B_4673) | ~m1_subset_1(A_4671, B_4673))), inference(resolution, [status(thm)], [c_28, c_149497])).
% 59.70/48.21  tff(c_150718, plain, (![A_4671]: (m1_subset_1(A_4671, '#skF_8') | v1_xboole_0('#skF_7') | ~m1_subset_1(A_4671, '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_150700])).
% 59.70/48.21  tff(c_150731, plain, (![A_4671]: (m1_subset_1(A_4671, '#skF_8') | ~m1_subset_1(A_4671, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_150218, c_150718])).
% 59.70/48.21  tff(c_168498, plain, (![A_5417, B_5418, C_5419]: (m1_subset_1('#skF_5'(A_5417, B_5418, C_5419), '#skF_8') | ~r1_tarski(B_5418, '#skF_7') | r2_lattice3(A_5417, B_5418, C_5419) | ~m1_subset_1(C_5419, u1_struct_0(A_5417)) | ~l1_orders_2(A_5417))), inference(resolution, [status(thm)], [c_168366, c_150731])).
% 59.70/48.21  tff(c_149451, plain, (![C_4558, B_4559, A_4560]: (~v1_xboole_0(C_4558) | ~m1_subset_1(B_4559, k1_zfmisc_1(C_4558)) | ~r2_hidden(A_4560, B_4559))), inference(cnfTransformation, [status(thm)], [f_77])).
% 59.70/48.21  tff(c_149459, plain, (![B_4561, A_4562, A_4563]: (~v1_xboole_0(B_4561) | ~r2_hidden(A_4562, A_4563) | ~r1_tarski(A_4563, B_4561))), inference(resolution, [status(thm)], [c_32, c_149451])).
% 59.70/48.21  tff(c_149483, plain, (![B_4569, A_4570]: (~v1_xboole_0(B_4569) | ~r1_tarski(A_4570, B_4569) | v1_xboole_0(A_4570))), inference(resolution, [status(thm)], [c_4, c_149459])).
% 59.70/48.21  tff(c_149495, plain, (~v1_xboole_0('#skF_8') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_60, c_149483])).
% 59.70/48.21  tff(c_149496, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_149495])).
% 59.70/48.21  tff(c_153141, plain, (![A_4845, B_4846, C_4847]: (m1_subset_1('#skF_5'(A_4845, B_4846, C_4847), B_4846) | r2_lattice3(A_4845, B_4846, C_4847) | ~m1_subset_1(C_4847, u1_struct_0(A_4845)) | ~l1_orders_2(A_4845))), inference(resolution, [status(thm)], [c_151010, c_26])).
% 59.70/48.21  tff(c_153284, plain, (![A_4851, C_4852]: (m1_subset_1('#skF_5'(A_4851, '#skF_7', C_4852), '#skF_8') | r2_lattice3(A_4851, '#skF_7', C_4852) | ~m1_subset_1(C_4852, u1_struct_0(A_4851)) | ~l1_orders_2(A_4851))), inference(resolution, [status(thm)], [c_153141, c_150731])).
% 59.70/48.21  tff(c_153289, plain, (![A_4851, C_4852]: (k6_domain_1('#skF_8', '#skF_5'(A_4851, '#skF_7', C_4852))=k1_tarski('#skF_5'(A_4851, '#skF_7', C_4852)) | v1_xboole_0('#skF_8') | r2_lattice3(A_4851, '#skF_7', C_4852) | ~m1_subset_1(C_4852, u1_struct_0(A_4851)) | ~l1_orders_2(A_4851))), inference(resolution, [status(thm)], [c_153284, c_40])).
% 59.70/48.21  tff(c_172282, plain, (![A_5542, C_5543]: (k6_domain_1('#skF_8', '#skF_5'(A_5542, '#skF_7', C_5543))=k1_tarski('#skF_5'(A_5542, '#skF_7', C_5543)) | r2_lattice3(A_5542, '#skF_7', C_5543) | ~m1_subset_1(C_5543, u1_struct_0(A_5542)) | ~l1_orders_2(A_5542))), inference(negUnitSimplification, [status(thm)], [c_149496, c_153289])).
% 59.70/48.21  tff(c_172347, plain, (k6_domain_1('#skF_8', '#skF_5'('#skF_6', '#skF_7', '#skF_9'))=k1_tarski('#skF_5'('#skF_6', '#skF_7', '#skF_9')) | r2_lattice3('#skF_6', '#skF_7', '#skF_9') | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_58, c_172282])).
% 59.70/48.21  tff(c_172366, plain, (k6_domain_1('#skF_8', '#skF_5'('#skF_6', '#skF_7', '#skF_9'))=k1_tarski('#skF_5'('#skF_6', '#skF_7', '#skF_9')) | r2_lattice3('#skF_6', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_172347])).
% 59.70/48.21  tff(c_172367, plain, (k6_domain_1('#skF_8', '#skF_5'('#skF_6', '#skF_7', '#skF_9'))=k1_tarski('#skF_5'('#skF_6', '#skF_7', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_149383, c_172366])).
% 59.70/48.21  tff(c_149601, plain, (![A_4584, B_4585]: (r1_tarski(k6_domain_1(A_4584, B_4585), A_4584) | ~m1_subset_1(B_4585, A_4584) | v1_xboole_0(A_4584))), inference(resolution, [status(thm)], [c_149584, c_30])).
% 59.70/48.21  tff(c_172407, plain, (r1_tarski(k1_tarski('#skF_5'('#skF_6', '#skF_7', '#skF_9')), '#skF_8') | ~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_9'), '#skF_8') | v1_xboole_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_172367, c_149601])).
% 59.70/48.21  tff(c_172434, plain, (r1_tarski(k1_tarski('#skF_5'('#skF_6', '#skF_7', '#skF_9')), '#skF_8') | ~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_149496, c_172407])).
% 59.70/48.21  tff(c_172437, plain, (~m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_172434])).
% 59.70/48.21  tff(c_172440, plain, (~r1_tarski('#skF_7', '#skF_7') | r2_lattice3('#skF_6', '#skF_7', '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_168498, c_172437])).
% 59.70/48.21  tff(c_172449, plain, (r2_lattice3('#skF_6', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_10, c_172440])).
% 59.70/48.21  tff(c_172451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149383, c_172449])).
% 59.70/48.21  tff(c_172453, plain, (m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_172434])).
% 59.70/48.21  tff(c_149338, plain, (r2_lattice3('#skF_6', '#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_68])).
% 59.70/48.21  tff(c_152161, plain, (![A_4782, D_4783, C_4784, B_4785]: (r1_orders_2(A_4782, D_4783, C_4784) | ~r2_hidden(D_4783, B_4785) | ~m1_subset_1(D_4783, u1_struct_0(A_4782)) | ~r2_lattice3(A_4782, B_4785, C_4784) | ~m1_subset_1(C_4784, u1_struct_0(A_4782)) | ~l1_orders_2(A_4782))), inference(cnfTransformation, [status(thm)], [f_119])).
% 60.08/48.21  tff(c_156124, plain, (![A_4982, A_4983, C_4984, B_4985]: (r1_orders_2(A_4982, A_4983, C_4984) | ~m1_subset_1(A_4983, u1_struct_0(A_4982)) | ~r2_lattice3(A_4982, B_4985, C_4984) | ~m1_subset_1(C_4984, u1_struct_0(A_4982)) | ~l1_orders_2(A_4982) | v1_xboole_0(B_4985) | ~m1_subset_1(A_4983, B_4985))), inference(resolution, [status(thm)], [c_28, c_152161])).
% 60.08/48.21  tff(c_202942, plain, (![A_6034, B_6033, B_6032, C_6035, C_6031]: (r1_orders_2(A_6034, '#skF_5'(A_6034, B_6033, C_6031), C_6035) | ~r2_lattice3(A_6034, B_6032, C_6035) | ~m1_subset_1(C_6035, u1_struct_0(A_6034)) | v1_xboole_0(B_6032) | ~m1_subset_1('#skF_5'(A_6034, B_6033, C_6031), B_6032) | r2_lattice3(A_6034, B_6033, C_6031) | ~m1_subset_1(C_6031, u1_struct_0(A_6034)) | ~l1_orders_2(A_6034))), inference(resolution, [status(thm)], [c_56, c_156124])).
% 60.08/48.21  tff(c_202964, plain, (![B_6033, C_6031]: (r1_orders_2('#skF_6', '#skF_5'('#skF_6', B_6033, C_6031), '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | v1_xboole_0('#skF_8') | ~m1_subset_1('#skF_5'('#skF_6', B_6033, C_6031), '#skF_8') | r2_lattice3('#skF_6', B_6033, C_6031) | ~m1_subset_1(C_6031, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_149338, c_202942])).
% 60.08/48.21  tff(c_202981, plain, (![B_6033, C_6031]: (r1_orders_2('#skF_6', '#skF_5'('#skF_6', B_6033, C_6031), '#skF_9') | v1_xboole_0('#skF_8') | ~m1_subset_1('#skF_5'('#skF_6', B_6033, C_6031), '#skF_8') | r2_lattice3('#skF_6', B_6033, C_6031) | ~m1_subset_1(C_6031, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_202964])).
% 60.08/48.21  tff(c_203063, plain, (![B_6039, C_6040]: (r1_orders_2('#skF_6', '#skF_5'('#skF_6', B_6039, C_6040), '#skF_9') | ~m1_subset_1('#skF_5'('#skF_6', B_6039, C_6040), '#skF_8') | r2_lattice3('#skF_6', B_6039, C_6040) | ~m1_subset_1(C_6040, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_149496, c_202981])).
% 60.08/48.21  tff(c_203067, plain, (![B_6039]: (~l1_orders_2('#skF_6') | ~m1_subset_1('#skF_5'('#skF_6', B_6039, '#skF_9'), '#skF_8') | r2_lattice3('#skF_6', B_6039, '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_203063, c_52])).
% 60.08/48.21  tff(c_203081, plain, (![B_6041]: (~m1_subset_1('#skF_5'('#skF_6', B_6041, '#skF_9'), '#skF_8') | r2_lattice3('#skF_6', B_6041, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_203067])).
% 60.08/48.21  tff(c_203100, plain, (r2_lattice3('#skF_6', '#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_172453, c_203081])).
% 60.08/48.21  tff(c_203138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149383, c_203100])).
% 60.08/48.21  tff(c_203139, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_149495])).
% 60.08/48.21  tff(c_203690, plain, (![A_6092, B_6093, C_6094]: (r2_hidden('#skF_5'(A_6092, B_6093, C_6094), B_6093) | r2_lattice3(A_6092, B_6093, C_6094) | ~m1_subset_1(C_6094, u1_struct_0(A_6092)) | ~l1_orders_2(A_6092))), inference(cnfTransformation, [status(thm)], [f_119])).
% 60.08/48.21  tff(c_203956, plain, (![B_6118, A_6119, C_6120]: (~v1_xboole_0(B_6118) | r2_lattice3(A_6119, B_6118, C_6120) | ~m1_subset_1(C_6120, u1_struct_0(A_6119)) | ~l1_orders_2(A_6119))), inference(resolution, [status(thm)], [c_203690, c_2])).
% 60.08/48.21  tff(c_203966, plain, (![B_6118]: (~v1_xboole_0(B_6118) | r2_lattice3('#skF_6', B_6118, '#skF_9') | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_203956])).
% 60.08/48.21  tff(c_203974, plain, (![B_6124]: (~v1_xboole_0(B_6124) | r2_lattice3('#skF_6', B_6124, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_203966])).
% 60.08/48.21  tff(c_203977, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_203974, c_149383])).
% 60.08/48.21  tff(c_203981, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_203139, c_203977])).
% 60.08/48.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 60.08/48.21  
% 60.08/48.21  Inference rules
% 60.08/48.21  ----------------------
% 60.08/48.21  #Ref     : 0
% 60.08/48.21  #Sup     : 42486
% 60.08/48.21  #Fact    : 0
% 60.08/48.21  #Define  : 0
% 60.08/48.21  #Split   : 201
% 60.08/48.21  #Chain   : 0
% 60.08/48.21  #Close   : 0
% 60.08/48.21  
% 60.08/48.21  Ordering : KBO
% 60.08/48.21  
% 60.08/48.21  Simplification rules
% 60.08/48.21  ----------------------
% 60.08/48.21  #Subsume      : 10085
% 60.08/48.21  #Demod        : 18661
% 60.08/48.21  #Tautology    : 8077
% 60.08/48.21  #SimpNegUnit  : 8527
% 60.08/48.21  #BackRed      : 0
% 60.08/48.21  
% 60.08/48.21  #Partial instantiations: 0
% 60.08/48.21  #Strategies tried      : 1
% 60.08/48.21  
% 60.08/48.21  Timing (in seconds)
% 60.08/48.21  ----------------------
% 60.08/48.21  Preprocessing        : 0.35
% 60.08/48.21  Parsing              : 0.19
% 60.08/48.21  CNF conversion       : 0.03
% 60.08/48.21  Main loop            : 47.00
% 60.08/48.21  Inferencing          : 6.23
% 60.08/48.21  Reduction            : 11.96
% 60.08/48.21  Demodulation         : 8.17
% 60.08/48.21  BG Simplification    : 0.63
% 60.08/48.21  Subsumption          : 25.70
% 60.08/48.21  Abstraction          : 1.08
% 60.08/48.21  MUC search           : 0.00
% 60.08/48.21  Cooper               : 0.00
% 60.08/48.21  Total                : 47.44
% 60.08/48.21  Index Insertion      : 0.00
% 60.08/48.22  Index Deletion       : 0.00
% 60.08/48.22  Index Matching       : 0.00
% 60.08/48.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
