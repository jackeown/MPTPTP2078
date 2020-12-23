%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1123+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:26 EST 2020

% Result     : Theorem 6.22s
% Output     : CNFRefutation 6.22s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 396 expanded)
%              Number of leaves         :   29 ( 137 expanded)
%              Depth                    :   17
%              Number of atoms          :  277 (1561 expanded)
%              Number of equality atoms :    1 (  12 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_hidden(C,k2_pre_topc(A,B))
                <=> ( ~ v2_struct_0(A)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & r2_hidden(C,D)
                            & r1_xboole_0(B,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = k2_pre_topc(A,B)
              <=> ! [D] :
                    ( r2_hidden(D,u1_struct_0(A))
                   => ( r2_hidden(D,C)
                    <=> ! [E] :
                          ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v3_pre_topc(E,A)
                              & r2_hidden(D,E)
                              & r1_xboole_0(B,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_36,plain,(
    ! [A_87] :
      ( l1_struct_0(A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_74,plain,
    ( r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5'))
    | ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_85,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_1402,plain,(
    ! [C_395,B_396,A_397] :
      ( ~ v1_xboole_0(C_395)
      | ~ m1_subset_1(B_396,k1_zfmisc_1(C_395))
      | ~ r2_hidden(A_397,B_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1405,plain,(
    ! [A_397] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_397,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_1402])).

tff(c_1406,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1405])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_42,plain,(
    ! [A_90,B_91] :
      ( r2_hidden(A_90,B_91)
      | v1_xboole_0(B_91)
      | ~ m1_subset_1(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    ! [A_85,B_86] :
      ( m1_subset_1(k2_pre_topc(A_85,B_86),k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_58,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | v2_struct_0('#skF_4')
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_92,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_58])).

tff(c_93,plain,(
    ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_103,plain,(
    ! [C_123,B_124,A_125] :
      ( ~ v1_xboole_0(C_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(C_123))
      | ~ r2_hidden(A_125,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_106,plain,(
    ! [A_125] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_125,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_103])).

tff(c_107,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_991,plain,(
    ! [D_340,A_341,B_342] :
      ( r2_hidden(D_340,'#skF_1'(A_341,B_342,k2_pre_topc(A_341,B_342),D_340))
      | r2_hidden(D_340,k2_pre_topc(A_341,B_342))
      | ~ r2_hidden(D_340,u1_struct_0(A_341))
      | ~ m1_subset_1(k2_pre_topc(A_341,B_342),k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ m1_subset_1(B_342,k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ l1_pre_topc(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_994,plain,(
    ! [D_340,A_85,B_86] :
      ( r2_hidden(D_340,'#skF_1'(A_85,B_86,k2_pre_topc(A_85,B_86),D_340))
      | r2_hidden(D_340,k2_pre_topc(A_85,B_86))
      | ~ r2_hidden(D_340,u1_struct_0(A_85))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_34,c_991])).

tff(c_986,plain,(
    ! [A_334,B_335,D_336] :
      ( v3_pre_topc('#skF_1'(A_334,B_335,k2_pre_topc(A_334,B_335),D_336),A_334)
      | r2_hidden(D_336,k2_pre_topc(A_334,B_335))
      | ~ r2_hidden(D_336,u1_struct_0(A_334))
      | ~ m1_subset_1(k2_pre_topc(A_334,B_335),k1_zfmisc_1(u1_struct_0(A_334)))
      | ~ m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0(A_334)))
      | ~ l1_pre_topc(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_989,plain,(
    ! [A_85,B_86,D_336] :
      ( v3_pre_topc('#skF_1'(A_85,B_86,k2_pre_topc(A_85,B_86),D_336),A_85)
      | r2_hidden(D_336,k2_pre_topc(A_85,B_86))
      | ~ r2_hidden(D_336,u1_struct_0(A_85))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_34,c_986])).

tff(c_1163,plain,(
    ! [A_355,B_356,D_357] :
      ( m1_subset_1('#skF_1'(A_355,B_356,k2_pre_topc(A_355,B_356),D_357),k1_zfmisc_1(u1_struct_0(A_355)))
      | r2_hidden(D_357,k2_pre_topc(A_355,B_356))
      | ~ r2_hidden(D_357,u1_struct_0(A_355))
      | ~ m1_subset_1(k2_pre_topc(A_355,B_356),k1_zfmisc_1(u1_struct_0(A_355)))
      | ~ m1_subset_1(B_356,k1_zfmisc_1(u1_struct_0(A_355)))
      | ~ l1_pre_topc(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_64,plain,(
    ! [D_115] :
      ( r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5'))
      | ~ r1_xboole_0('#skF_5',D_115)
      | ~ r2_hidden('#skF_6',D_115)
      | ~ v3_pre_topc(D_115,'#skF_4')
      | ~ m1_subset_1(D_115,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_749,plain,(
    ! [D_115] :
      ( ~ r1_xboole_0('#skF_5',D_115)
      | ~ r2_hidden('#skF_6',D_115)
      | ~ v3_pre_topc(D_115,'#skF_4')
      | ~ m1_subset_1(D_115,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_64])).

tff(c_1193,plain,(
    ! [B_356,D_357] :
      ( ~ r1_xboole_0('#skF_5','#skF_1'('#skF_4',B_356,k2_pre_topc('#skF_4',B_356),D_357))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_356,k2_pre_topc('#skF_4',B_356),D_357))
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_356,k2_pre_topc('#skF_4',B_356),D_357),'#skF_4')
      | r2_hidden(D_357,k2_pre_topc('#skF_4',B_356))
      | ~ r2_hidden(D_357,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',B_356),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_356,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1163,c_749])).

tff(c_1272,plain,(
    ! [B_383,D_384] :
      ( ~ r1_xboole_0('#skF_5','#skF_1'('#skF_4',B_383,k2_pre_topc('#skF_4',B_383),D_384))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_383,k2_pre_topc('#skF_4',B_383),D_384))
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_383,k2_pre_topc('#skF_4',B_383),D_384),'#skF_4')
      | r2_hidden(D_384,k2_pre_topc('#skF_4',B_383))
      | ~ r2_hidden(D_384,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',B_383),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_383,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1193])).

tff(c_1281,plain,(
    ! [B_86,D_336] :
      ( ~ r1_xboole_0('#skF_5','#skF_1'('#skF_4',B_86,k2_pre_topc('#skF_4',B_86),D_336))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_86,k2_pre_topc('#skF_4',B_86),D_336))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',B_86),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden(D_336,k2_pre_topc('#skF_4',B_86))
      | ~ r2_hidden(D_336,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_989,c_1272])).

tff(c_1289,plain,(
    ! [B_385,D_386] :
      ( ~ r1_xboole_0('#skF_5','#skF_1'('#skF_4',B_385,k2_pre_topc('#skF_4',B_385),D_386))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_385,k2_pre_topc('#skF_4',B_385),D_386))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',B_385),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden(D_386,k2_pre_topc('#skF_4',B_385))
      | ~ r2_hidden(D_386,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_385,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1281])).

tff(c_1298,plain,(
    ! [B_86] :
      ( ~ r1_xboole_0('#skF_5','#skF_1'('#skF_4',B_86,k2_pre_topc('#skF_4',B_86),'#skF_6'))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',B_86),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden('#skF_6',k2_pre_topc('#skF_4',B_86))
      | ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_994,c_1289])).

tff(c_1308,plain,(
    ! [B_86] :
      ( ~ r1_xboole_0('#skF_5','#skF_1'('#skF_4',B_86,k2_pre_topc('#skF_4',B_86),'#skF_6'))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',B_86),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden('#skF_6',k2_pre_topc('#skF_4',B_86))
      | ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1298])).

tff(c_1310,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1308])).

tff(c_1313,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_1310])).

tff(c_1316,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1313])).

tff(c_1318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_1316])).

tff(c_1320,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1308])).

tff(c_944,plain,(
    ! [B_319,A_320,D_321] :
      ( r1_xboole_0(B_319,'#skF_1'(A_320,B_319,k2_pre_topc(A_320,B_319),D_321))
      | r2_hidden(D_321,k2_pre_topc(A_320,B_319))
      | ~ r2_hidden(D_321,u1_struct_0(A_320))
      | ~ m1_subset_1(k2_pre_topc(A_320,B_319),k1_zfmisc_1(u1_struct_0(A_320)))
      | ~ m1_subset_1(B_319,k1_zfmisc_1(u1_struct_0(A_320)))
      | ~ l1_pre_topc(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_947,plain,(
    ! [B_86,A_85,D_321] :
      ( r1_xboole_0(B_86,'#skF_1'(A_85,B_86,k2_pre_topc(A_85,B_86),D_321))
      | r2_hidden(D_321,k2_pre_topc(A_85,B_86))
      | ~ r2_hidden(D_321,u1_struct_0(A_85))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_34,c_944])).

tff(c_1325,plain,(
    ! [B_387] :
      ( ~ r1_xboole_0('#skF_5','#skF_1'('#skF_4',B_387,k2_pre_topc('#skF_4',B_387),'#skF_6'))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',B_387),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden('#skF_6',k2_pre_topc('#skF_4',B_387))
      | ~ m1_subset_1(B_387,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_1308])).

tff(c_1334,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_947,c_1325])).

tff(c_1341,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1320,c_1334])).

tff(c_1342,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_1341])).

tff(c_1360,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_1342])).

tff(c_1364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1360])).

tff(c_1366,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_40,plain,(
    ! [A_89] :
      ( ~ v1_xboole_0(u1_struct_0(A_89))
      | ~ l1_struct_0(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1375,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1366,c_40])).

tff(c_1378,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_1375])).

tff(c_1382,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1378])).

tff(c_1386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1382])).

tff(c_1388,plain,(
    r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_62,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4')
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1418,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1388,c_62])).

tff(c_1419,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_1418])).

tff(c_60,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1415,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1388,c_60])).

tff(c_1416,plain,(
    v3_pre_topc('#skF_7','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_1415])).

tff(c_1387,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_56,plain,
    ( r1_xboole_0('#skF_5','#skF_7')
    | v2_struct_0('#skF_4')
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1412,plain,
    ( r1_xboole_0('#skF_5','#skF_7')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1388,c_56])).

tff(c_1413,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_1412])).

tff(c_2032,plain,(
    ! [B_501,E_502,D_503,A_504] :
      ( ~ r1_xboole_0(B_501,E_502)
      | ~ r2_hidden(D_503,E_502)
      | ~ v3_pre_topc(E_502,A_504)
      | ~ m1_subset_1(E_502,k1_zfmisc_1(u1_struct_0(A_504)))
      | ~ r2_hidden(D_503,k2_pre_topc(A_504,B_501))
      | ~ r2_hidden(D_503,u1_struct_0(A_504))
      | ~ m1_subset_1(k2_pre_topc(A_504,B_501),k1_zfmisc_1(u1_struct_0(A_504)))
      | ~ m1_subset_1(B_501,k1_zfmisc_1(u1_struct_0(A_504)))
      | ~ l1_pre_topc(A_504) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2042,plain,(
    ! [D_505,A_506] :
      ( ~ r2_hidden(D_505,'#skF_7')
      | ~ v3_pre_topc('#skF_7',A_506)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_506)))
      | ~ r2_hidden(D_505,k2_pre_topc(A_506,'#skF_5'))
      | ~ r2_hidden(D_505,u1_struct_0(A_506))
      | ~ m1_subset_1(k2_pre_topc(A_506,'#skF_5'),k1_zfmisc_1(u1_struct_0(A_506)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_506)))
      | ~ l1_pre_topc(A_506) ) ),
    inference(resolution,[status(thm)],[c_1413,c_2032])).

tff(c_2047,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | ~ v3_pre_topc('#skF_7','#skF_4')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1388,c_2042])).

tff(c_2051,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1419,c_1416,c_1387,c_2047])).

tff(c_2052,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_2051])).

tff(c_2055,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_2052])).

tff(c_2059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2055])).

tff(c_2060,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2051])).

tff(c_2072,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_2060])).

tff(c_2075,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2072])).

tff(c_2077,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1406,c_2075])).

tff(c_2079,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1405])).

tff(c_2088,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2079,c_40])).

tff(c_2091,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_2088])).

tff(c_2094,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_2091])).

tff(c_2098,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2094])).

tff(c_2100,plain,(
    v2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_38,plain,(
    ! [A_88] :
      ( v1_xboole_0(u1_struct_0(A_88))
      | ~ l1_struct_0(A_88)
      | ~ v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2118,plain,(
    ! [C_514,B_515,A_516] :
      ( ~ v1_xboole_0(C_514)
      | ~ m1_subset_1(B_515,k1_zfmisc_1(C_514))
      | ~ r2_hidden(A_516,B_515) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2121,plain,(
    ! [A_516] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_516,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_2118])).

tff(c_2122,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2121])).

tff(c_2125,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_2122])).

tff(c_2128,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2100,c_2125])).

tff(c_2131,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_2128])).

tff(c_2135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2131])).

tff(c_2137,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2121])).

tff(c_2099,plain,(
    r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_2157,plain,(
    ! [A_519,B_520] :
      ( m1_subset_1(k2_pre_topc(A_519,B_520),k1_zfmisc_1(u1_struct_0(A_519)))
      | ~ m1_subset_1(B_520,k1_zfmisc_1(u1_struct_0(A_519)))
      | ~ l1_pre_topc(A_519) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    ! [C_94,B_93,A_92] :
      ( ~ v1_xboole_0(C_94)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(C_94))
      | ~ r2_hidden(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2161,plain,(
    ! [A_521,A_522,B_523] :
      ( ~ v1_xboole_0(u1_struct_0(A_521))
      | ~ r2_hidden(A_522,k2_pre_topc(A_521,B_523))
      | ~ m1_subset_1(B_523,k1_zfmisc_1(u1_struct_0(A_521)))
      | ~ l1_pre_topc(A_521) ) ),
    inference(resolution,[status(thm)],[c_2157,c_44])).

tff(c_2166,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_2099,c_2161])).

tff(c_2171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2137,c_2166])).

%------------------------------------------------------------------------------
