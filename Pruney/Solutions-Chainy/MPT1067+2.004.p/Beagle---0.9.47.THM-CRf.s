%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:40 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 124 expanded)
%              Number of leaves         :   29 (  57 expanded)
%              Depth                    :   20
%              Number of atoms          :  191 ( 366 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > v1_funct_1 > k7_funct_2 > k6_funct_2 > k5_setfam_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k6_funct_2,type,(
    k6_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k7_funct_2,type,(
    k7_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A)))
                   => r1_tarski(k5_setfam_1(A,D),k5_setfam_1(A,k6_funct_2(A,B,C,k7_funct_2(A,B,C,D)))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_funct_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A)))
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(A))
                     => ( m1_setfam_1(D,E)
                       => m1_setfam_1(k6_funct_2(A,B,C,k7_funct_2(A,B,C,D)),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A))) )
     => m1_subset_1(k7_funct_2(A,B,C,D),k1_zfmisc_1(k1_zfmisc_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(B))) )
     => m1_subset_1(k6_funct_2(A,B,C,D),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_funct_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_52,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,B_65)
      | ~ m1_subset_1(A_64,k1_zfmisc_1(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_60,plain,(
    r1_tarski('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_52])).

tff(c_10,plain,(
    ! [A_5] : k3_tarski(k1_zfmisc_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(k3_tarski(A_72),k3_tarski(B_73))
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [A_72,A_5] :
      ( r1_tarski(k3_tarski(A_72),A_5)
      | ~ r1_tarski(A_72,k1_zfmisc_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_83])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_59,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_52])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_34,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [B_70,A_71] :
      ( m1_setfam_1(B_70,A_71)
      | ~ r1_tarski(A_71,k3_tarski(B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_82,plain,(
    ! [B_70] : m1_setfam_1(B_70,k3_tarski(B_70)) ),
    inference(resolution,[status(thm)],[c_6,c_70])).

tff(c_389,plain,(
    ! [E_121,C_125,D_122,A_123,B_124] :
      ( m1_setfam_1(k6_funct_2(A_123,B_124,C_125,k7_funct_2(A_123,B_124,C_125,D_122)),E_121)
      | ~ m1_setfam_1(D_122,E_121)
      | ~ m1_subset_1(E_121,k1_zfmisc_1(A_123))
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k1_zfmisc_1(A_123)))
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124)))
      | ~ v1_funct_2(C_125,A_123,B_124)
      | ~ v1_funct_1(C_125)
      | v1_xboole_0(B_124)
      | v1_xboole_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1534,plain,(
    ! [C_233,A_234,A_237,E_236,B_235] :
      ( m1_setfam_1(k6_funct_2(A_234,B_235,C_233,k7_funct_2(A_234,B_235,C_233,A_237)),E_236)
      | ~ m1_setfam_1(A_237,E_236)
      | ~ m1_subset_1(E_236,k1_zfmisc_1(A_234))
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ v1_funct_2(C_233,A_234,B_235)
      | ~ v1_funct_1(C_233)
      | v1_xboole_0(B_235)
      | v1_xboole_0(A_234)
      | ~ r1_tarski(A_237,k1_zfmisc_1(A_234)) ) ),
    inference(resolution,[status(thm)],[c_20,c_389])).

tff(c_1540,plain,(
    ! [A_10,A_234,A_237,E_236,B_235] :
      ( m1_setfam_1(k6_funct_2(A_234,B_235,A_10,k7_funct_2(A_234,B_235,A_10,A_237)),E_236)
      | ~ m1_setfam_1(A_237,E_236)
      | ~ m1_subset_1(E_236,k1_zfmisc_1(A_234))
      | ~ v1_funct_2(A_10,A_234,B_235)
      | ~ v1_funct_1(A_10)
      | v1_xboole_0(B_235)
      | v1_xboole_0(A_234)
      | ~ r1_tarski(A_237,k1_zfmisc_1(A_234))
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_234,B_235)) ) ),
    inference(resolution,[status(thm)],[c_20,c_1534])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,k3_tarski(B_7))
      | ~ m1_setfam_1(B_7,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_240,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( m1_subset_1(k7_funct_2(A_100,B_101,C_102,D_103),k1_zfmisc_1(k1_zfmisc_1(B_101)))
      | ~ m1_subset_1(D_103,k1_zfmisc_1(k1_zfmisc_1(A_100)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ v1_funct_2(C_102,A_100,B_101)
      | ~ v1_funct_1(C_102)
      | v1_xboole_0(B_101)
      | v1_xboole_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_248,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( r1_tarski(k7_funct_2(A_100,B_101,C_102,D_103),k1_zfmisc_1(B_101))
      | ~ m1_subset_1(D_103,k1_zfmisc_1(k1_zfmisc_1(A_100)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ v1_funct_2(C_102,A_100,B_101)
      | ~ v1_funct_1(C_102)
      | v1_xboole_0(B_101)
      | v1_xboole_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_240,c_18])).

tff(c_362,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( m1_subset_1(k6_funct_2(A_115,B_116,C_117,D_118),k1_zfmisc_1(k1_zfmisc_1(A_115)))
      | ~ m1_subset_1(D_118,k1_zfmisc_1(k1_zfmisc_1(B_116)))
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_2(C_117,A_115,B_116)
      | ~ v1_funct_1(C_117)
      | v1_xboole_0(B_116)
      | v1_xboole_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( k5_setfam_1(A_8,B_9) = k3_tarski(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k1_zfmisc_1(A_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1116,plain,(
    ! [A_193,B_194,C_195,D_196] :
      ( k5_setfam_1(A_193,k6_funct_2(A_193,B_194,C_195,D_196)) = k3_tarski(k6_funct_2(A_193,B_194,C_195,D_196))
      | ~ m1_subset_1(D_196,k1_zfmisc_1(k1_zfmisc_1(B_194)))
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194)))
      | ~ v1_funct_2(C_195,A_193,B_194)
      | ~ v1_funct_1(C_195)
      | v1_xboole_0(B_194)
      | v1_xboole_0(A_193) ) ),
    inference(resolution,[status(thm)],[c_362,c_16])).

tff(c_2356,plain,(
    ! [A_303,B_304,C_305,A_306] :
      ( k5_setfam_1(A_303,k6_funct_2(A_303,B_304,C_305,A_306)) = k3_tarski(k6_funct_2(A_303,B_304,C_305,A_306))
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_303,B_304)))
      | ~ v1_funct_2(C_305,A_303,B_304)
      | ~ v1_funct_1(C_305)
      | v1_xboole_0(B_304)
      | v1_xboole_0(A_303)
      | ~ r1_tarski(A_306,k1_zfmisc_1(B_304)) ) ),
    inference(resolution,[status(thm)],[c_20,c_1116])).

tff(c_2361,plain,(
    ! [A_306] :
      ( k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',A_306)) = k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3',A_306))
      | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_1('#skF_3')
      | v1_xboole_0('#skF_2')
      | v1_xboole_0('#skF_1')
      | ~ r1_tarski(A_306,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_32,c_2356])).

tff(c_2365,plain,(
    ! [A_306] :
      ( k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',A_306)) = k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3',A_306))
      | v1_xboole_0('#skF_2')
      | v1_xboole_0('#skF_1')
      | ~ r1_tarski(A_306,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_2361])).

tff(c_2451,plain,(
    ! [A_313] :
      ( k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',A_313)) = k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3',A_313))
      | ~ r1_tarski(A_313,k1_zfmisc_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_2365])).

tff(c_2467,plain,(
    ! [A_100,C_102,D_103] :
      ( k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2(A_100,'#skF_2',C_102,D_103))) = k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2(A_100,'#skF_2',C_102,D_103)))
      | ~ m1_subset_1(D_103,k1_zfmisc_1(k1_zfmisc_1(A_100)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,'#skF_2')))
      | ~ v1_funct_2(C_102,A_100,'#skF_2')
      | ~ v1_funct_1(C_102)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_248,c_2451])).

tff(c_3393,plain,(
    ! [A_389,C_390,D_391] :
      ( k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2(A_389,'#skF_2',C_390,D_391))) = k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2(A_389,'#skF_2',C_390,D_391)))
      | ~ m1_subset_1(D_391,k1_zfmisc_1(k1_zfmisc_1(A_389)))
      | ~ m1_subset_1(C_390,k1_zfmisc_1(k2_zfmisc_1(A_389,'#skF_2')))
      | ~ v1_funct_2(C_390,A_389,'#skF_2')
      | ~ v1_funct_1(C_390)
      | v1_xboole_0(A_389) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2467])).

tff(c_3402,plain,(
    ! [C_390] :
      ( k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2',C_390,'#skF_4'))) = k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2',C_390,'#skF_4')))
      | ~ m1_subset_1(C_390,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_2(C_390,'#skF_1','#skF_2')
      | ~ v1_funct_1(C_390)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_3393])).

tff(c_3781,plain,(
    ! [C_414] :
      ( k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2',C_414,'#skF_4'))) = k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2',C_414,'#skF_4')))
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_2(C_414,'#skF_1','#skF_2')
      | ~ v1_funct_1(C_414) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_3402])).

tff(c_3788,plain,
    ( k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) = k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_3781])).

tff(c_3792,plain,(
    k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) = k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_3788])).

tff(c_157,plain,(
    ! [A_86,B_87] :
      ( k5_setfam_1(A_86,B_87) = k3_tarski(B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k1_zfmisc_1(A_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_166,plain,(
    k5_setfam_1('#skF_1','#skF_4') = k3_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_157])).

tff(c_28,plain,(
    ~ r1_tarski(k5_setfam_1('#skF_1','#skF_4'),k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_167,plain,(
    ~ r1_tarski(k3_tarski('#skF_4'),k5_setfam_1('#skF_1',k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_28])).

tff(c_4742,plain,(
    ~ r1_tarski(k3_tarski('#skF_4'),k3_tarski(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3792,c_167])).

tff(c_4758,plain,(
    ~ m1_setfam_1(k6_funct_2('#skF_1','#skF_2','#skF_3',k7_funct_2('#skF_1','#skF_2','#skF_3','#skF_4')),k3_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_12,c_4742])).

tff(c_4761,plain,
    ( ~ m1_setfam_1('#skF_4',k3_tarski('#skF_4'))
    | ~ m1_subset_1(k3_tarski('#skF_4'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1')
    | ~ r1_tarski('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1540,c_4758])).

tff(c_4776,plain,
    ( ~ m1_subset_1(k3_tarski('#skF_4'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_60,c_36,c_34,c_82,c_4761])).

tff(c_4777,plain,(
    ~ m1_subset_1(k3_tarski('#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_4776])).

tff(c_4792,plain,(
    ~ r1_tarski(k3_tarski('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_4777])).

tff(c_4826,plain,(
    ~ r1_tarski('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_92,c_4792])).

tff(c_4830,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4826])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.49/2.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/2.58  
% 7.49/2.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/2.58  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > v1_funct_1 > k7_funct_2 > k6_funct_2 > k5_setfam_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.49/2.58  
% 7.49/2.58  %Foreground sorts:
% 7.49/2.58  
% 7.49/2.58  
% 7.49/2.58  %Background operators:
% 7.49/2.58  
% 7.49/2.58  
% 7.49/2.58  %Foreground operators:
% 7.49/2.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.49/2.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.49/2.58  tff(k6_funct_2, type, k6_funct_2: ($i * $i * $i * $i) > $i).
% 7.49/2.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.49/2.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.49/2.58  tff('#skF_2', type, '#skF_2': $i).
% 7.49/2.58  tff('#skF_3', type, '#skF_3': $i).
% 7.49/2.58  tff('#skF_1', type, '#skF_1': $i).
% 7.49/2.58  tff(k7_funct_2, type, k7_funct_2: ($i * $i * $i * $i) > $i).
% 7.49/2.58  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 7.49/2.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.49/2.58  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 7.49/2.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.49/2.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.49/2.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.49/2.58  tff('#skF_4', type, '#skF_4': $i).
% 7.49/2.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.49/2.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.49/2.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.49/2.58  
% 7.65/2.60  tff(f_125, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A))) => r1_tarski(k5_setfam_1(A, D), k5_setfam_1(A, k6_funct_2(A, B, C, k7_funct_2(A, B, C, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t184_funct_2)).
% 7.65/2.60  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.65/2.60  tff(f_37, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 7.65/2.60  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 7.65/2.60  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.65/2.60  tff(f_41, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 7.65/2.60  tff(f_105, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(A)) => (m1_setfam_1(D, E) => m1_setfam_1(k6_funct_2(A, B, C, k7_funct_2(A, B, C, D)), E)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_funct_2)).
% 7.65/2.60  tff(f_81, axiom, (![A, B, C, D]: ((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A)))) => m1_subset_1(k7_funct_2(A, B, C, D), k1_zfmisc_1(k1_zfmisc_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_funct_2)).
% 7.65/2.60  tff(f_65, axiom, (![A, B, C, D]: ((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(B)))) => m1_subset_1(k6_funct_2(A, B, C, D), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_funct_2)).
% 7.65/2.60  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 7.65/2.60  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.65/2.60  tff(c_52, plain, (![A_64, B_65]: (r1_tarski(A_64, B_65) | ~m1_subset_1(A_64, k1_zfmisc_1(B_65)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.65/2.60  tff(c_60, plain, (r1_tarski('#skF_4', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_52])).
% 7.65/2.60  tff(c_10, plain, (![A_5]: (k3_tarski(k1_zfmisc_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.65/2.60  tff(c_83, plain, (![A_72, B_73]: (r1_tarski(k3_tarski(A_72), k3_tarski(B_73)) | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.65/2.60  tff(c_92, plain, (![A_72, A_5]: (r1_tarski(k3_tarski(A_72), A_5) | ~r1_tarski(A_72, k1_zfmisc_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_83])).
% 7.65/2.60  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.65/2.60  tff(c_40, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.65/2.60  tff(c_38, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.65/2.60  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.65/2.60  tff(c_59, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_52])).
% 7.65/2.60  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.65/2.60  tff(c_34, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.65/2.60  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.65/2.60  tff(c_70, plain, (![B_70, A_71]: (m1_setfam_1(B_70, A_71) | ~r1_tarski(A_71, k3_tarski(B_70)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.65/2.60  tff(c_82, plain, (![B_70]: (m1_setfam_1(B_70, k3_tarski(B_70)))), inference(resolution, [status(thm)], [c_6, c_70])).
% 7.65/2.60  tff(c_389, plain, (![E_121, C_125, D_122, A_123, B_124]: (m1_setfam_1(k6_funct_2(A_123, B_124, C_125, k7_funct_2(A_123, B_124, C_125, D_122)), E_121) | ~m1_setfam_1(D_122, E_121) | ~m1_subset_1(E_121, k1_zfmisc_1(A_123)) | ~m1_subset_1(D_122, k1_zfmisc_1(k1_zfmisc_1(A_123))) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))) | ~v1_funct_2(C_125, A_123, B_124) | ~v1_funct_1(C_125) | v1_xboole_0(B_124) | v1_xboole_0(A_123))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.65/2.60  tff(c_1534, plain, (![C_233, A_234, A_237, E_236, B_235]: (m1_setfam_1(k6_funct_2(A_234, B_235, C_233, k7_funct_2(A_234, B_235, C_233, A_237)), E_236) | ~m1_setfam_1(A_237, E_236) | ~m1_subset_1(E_236, k1_zfmisc_1(A_234)) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))) | ~v1_funct_2(C_233, A_234, B_235) | ~v1_funct_1(C_233) | v1_xboole_0(B_235) | v1_xboole_0(A_234) | ~r1_tarski(A_237, k1_zfmisc_1(A_234)))), inference(resolution, [status(thm)], [c_20, c_389])).
% 7.65/2.60  tff(c_1540, plain, (![A_10, A_234, A_237, E_236, B_235]: (m1_setfam_1(k6_funct_2(A_234, B_235, A_10, k7_funct_2(A_234, B_235, A_10, A_237)), E_236) | ~m1_setfam_1(A_237, E_236) | ~m1_subset_1(E_236, k1_zfmisc_1(A_234)) | ~v1_funct_2(A_10, A_234, B_235) | ~v1_funct_1(A_10) | v1_xboole_0(B_235) | v1_xboole_0(A_234) | ~r1_tarski(A_237, k1_zfmisc_1(A_234)) | ~r1_tarski(A_10, k2_zfmisc_1(A_234, B_235)))), inference(resolution, [status(thm)], [c_20, c_1534])).
% 7.65/2.60  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(A_6, k3_tarski(B_7)) | ~m1_setfam_1(B_7, A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.65/2.60  tff(c_240, plain, (![A_100, B_101, C_102, D_103]: (m1_subset_1(k7_funct_2(A_100, B_101, C_102, D_103), k1_zfmisc_1(k1_zfmisc_1(B_101))) | ~m1_subset_1(D_103, k1_zfmisc_1(k1_zfmisc_1(A_100))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~v1_funct_2(C_102, A_100, B_101) | ~v1_funct_1(C_102) | v1_xboole_0(B_101) | v1_xboole_0(A_100))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.65/2.60  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.65/2.60  tff(c_248, plain, (![A_100, B_101, C_102, D_103]: (r1_tarski(k7_funct_2(A_100, B_101, C_102, D_103), k1_zfmisc_1(B_101)) | ~m1_subset_1(D_103, k1_zfmisc_1(k1_zfmisc_1(A_100))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~v1_funct_2(C_102, A_100, B_101) | ~v1_funct_1(C_102) | v1_xboole_0(B_101) | v1_xboole_0(A_100))), inference(resolution, [status(thm)], [c_240, c_18])).
% 7.65/2.60  tff(c_362, plain, (![A_115, B_116, C_117, D_118]: (m1_subset_1(k6_funct_2(A_115, B_116, C_117, D_118), k1_zfmisc_1(k1_zfmisc_1(A_115))) | ~m1_subset_1(D_118, k1_zfmisc_1(k1_zfmisc_1(B_116))) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_2(C_117, A_115, B_116) | ~v1_funct_1(C_117) | v1_xboole_0(B_116) | v1_xboole_0(A_115))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.65/2.60  tff(c_16, plain, (![A_8, B_9]: (k5_setfam_1(A_8, B_9)=k3_tarski(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(k1_zfmisc_1(A_8))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.65/2.60  tff(c_1116, plain, (![A_193, B_194, C_195, D_196]: (k5_setfam_1(A_193, k6_funct_2(A_193, B_194, C_195, D_196))=k3_tarski(k6_funct_2(A_193, B_194, C_195, D_196)) | ~m1_subset_1(D_196, k1_zfmisc_1(k1_zfmisc_1(B_194))) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))) | ~v1_funct_2(C_195, A_193, B_194) | ~v1_funct_1(C_195) | v1_xboole_0(B_194) | v1_xboole_0(A_193))), inference(resolution, [status(thm)], [c_362, c_16])).
% 7.65/2.60  tff(c_2356, plain, (![A_303, B_304, C_305, A_306]: (k5_setfam_1(A_303, k6_funct_2(A_303, B_304, C_305, A_306))=k3_tarski(k6_funct_2(A_303, B_304, C_305, A_306)) | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_303, B_304))) | ~v1_funct_2(C_305, A_303, B_304) | ~v1_funct_1(C_305) | v1_xboole_0(B_304) | v1_xboole_0(A_303) | ~r1_tarski(A_306, k1_zfmisc_1(B_304)))), inference(resolution, [status(thm)], [c_20, c_1116])).
% 7.65/2.60  tff(c_2361, plain, (![A_306]: (k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', A_306))=k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', A_306)) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1') | ~r1_tarski(A_306, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_32, c_2356])).
% 7.65/2.60  tff(c_2365, plain, (![A_306]: (k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', A_306))=k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', A_306)) | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1') | ~r1_tarski(A_306, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_2361])).
% 7.65/2.60  tff(c_2451, plain, (![A_313]: (k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', A_313))=k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', A_313)) | ~r1_tarski(A_313, k1_zfmisc_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_2365])).
% 7.65/2.60  tff(c_2467, plain, (![A_100, C_102, D_103]: (k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2(A_100, '#skF_2', C_102, D_103)))=k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2(A_100, '#skF_2', C_102, D_103))) | ~m1_subset_1(D_103, k1_zfmisc_1(k1_zfmisc_1(A_100))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, '#skF_2'))) | ~v1_funct_2(C_102, A_100, '#skF_2') | ~v1_funct_1(C_102) | v1_xboole_0('#skF_2') | v1_xboole_0(A_100))), inference(resolution, [status(thm)], [c_248, c_2451])).
% 7.65/2.60  tff(c_3393, plain, (![A_389, C_390, D_391]: (k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2(A_389, '#skF_2', C_390, D_391)))=k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2(A_389, '#skF_2', C_390, D_391))) | ~m1_subset_1(D_391, k1_zfmisc_1(k1_zfmisc_1(A_389))) | ~m1_subset_1(C_390, k1_zfmisc_1(k2_zfmisc_1(A_389, '#skF_2'))) | ~v1_funct_2(C_390, A_389, '#skF_2') | ~v1_funct_1(C_390) | v1_xboole_0(A_389))), inference(negUnitSimplification, [status(thm)], [c_38, c_2467])).
% 7.65/2.60  tff(c_3402, plain, (![C_390]: (k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', C_390, '#skF_4')))=k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', C_390, '#skF_4'))) | ~m1_subset_1(C_390, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2(C_390, '#skF_1', '#skF_2') | ~v1_funct_1(C_390) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_3393])).
% 7.65/2.60  tff(c_3781, plain, (![C_414]: (k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', C_414, '#skF_4')))=k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', C_414, '#skF_4'))) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2(C_414, '#skF_1', '#skF_2') | ~v1_funct_1(C_414))), inference(negUnitSimplification, [status(thm)], [c_40, c_3402])).
% 7.65/2.60  tff(c_3788, plain, (k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))=k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_3781])).
% 7.65/2.60  tff(c_3792, plain, (k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))=k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_3788])).
% 7.65/2.60  tff(c_157, plain, (![A_86, B_87]: (k5_setfam_1(A_86, B_87)=k3_tarski(B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(k1_zfmisc_1(A_86))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.65/2.60  tff(c_166, plain, (k5_setfam_1('#skF_1', '#skF_4')=k3_tarski('#skF_4')), inference(resolution, [status(thm)], [c_30, c_157])).
% 7.65/2.60  tff(c_28, plain, (~r1_tarski(k5_setfam_1('#skF_1', '#skF_4'), k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.65/2.60  tff(c_167, plain, (~r1_tarski(k3_tarski('#skF_4'), k5_setfam_1('#skF_1', k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_28])).
% 7.65/2.60  tff(c_4742, plain, (~r1_tarski(k3_tarski('#skF_4'), k3_tarski(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_3792, c_167])).
% 7.65/2.60  tff(c_4758, plain, (~m1_setfam_1(k6_funct_2('#skF_1', '#skF_2', '#skF_3', k7_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')), k3_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_4742])).
% 7.65/2.60  tff(c_4761, plain, (~m1_setfam_1('#skF_4', k3_tarski('#skF_4')) | ~m1_subset_1(k3_tarski('#skF_4'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1') | ~r1_tarski('#skF_4', k1_zfmisc_1('#skF_1')) | ~r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1540, c_4758])).
% 7.65/2.60  tff(c_4776, plain, (~m1_subset_1(k3_tarski('#skF_4'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_60, c_36, c_34, c_82, c_4761])).
% 7.65/2.60  tff(c_4777, plain, (~m1_subset_1(k3_tarski('#skF_4'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_4776])).
% 7.65/2.60  tff(c_4792, plain, (~r1_tarski(k3_tarski('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_20, c_4777])).
% 7.65/2.60  tff(c_4826, plain, (~r1_tarski('#skF_4', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_92, c_4792])).
% 7.65/2.60  tff(c_4830, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_4826])).
% 7.65/2.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.60  
% 7.65/2.60  Inference rules
% 7.65/2.60  ----------------------
% 7.65/2.60  #Ref     : 0
% 7.65/2.60  #Sup     : 1006
% 7.65/2.60  #Fact    : 0
% 7.65/2.60  #Define  : 0
% 7.65/2.60  #Split   : 3
% 7.65/2.60  #Chain   : 0
% 7.65/2.60  #Close   : 0
% 7.65/2.60  
% 7.65/2.60  Ordering : KBO
% 7.65/2.60  
% 7.65/2.60  Simplification rules
% 7.65/2.60  ----------------------
% 7.65/2.60  #Subsume      : 140
% 7.65/2.60  #Demod        : 424
% 7.65/2.60  #Tautology    : 159
% 7.65/2.60  #SimpNegUnit  : 26
% 7.65/2.60  #BackRed      : 3
% 7.65/2.60  
% 7.65/2.60  #Partial instantiations: 0
% 7.65/2.60  #Strategies tried      : 1
% 7.65/2.60  
% 7.65/2.60  Timing (in seconds)
% 7.65/2.60  ----------------------
% 7.65/2.60  Preprocessing        : 0.33
% 7.65/2.61  Parsing              : 0.17
% 7.65/2.61  CNF conversion       : 0.03
% 7.65/2.61  Main loop            : 1.50
% 7.65/2.61  Inferencing          : 0.40
% 7.65/2.61  Reduction            : 0.33
% 7.65/2.61  Demodulation         : 0.22
% 7.65/2.61  BG Simplification    : 0.05
% 7.65/2.61  Subsumption          : 0.62
% 7.65/2.61  Abstraction          : 0.08
% 7.65/2.61  MUC search           : 0.00
% 7.65/2.61  Cooper               : 0.00
% 7.65/2.61  Total                : 1.87
% 7.65/2.61  Index Insertion      : 0.00
% 7.65/2.61  Index Deletion       : 0.00
% 7.65/2.61  Index Matching       : 0.00
% 7.65/2.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
