%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:16 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 711 expanded)
%              Number of leaves         :   36 ( 296 expanded)
%              Depth                    :   19
%              Number of atoms          :  295 (5171 expanded)
%              Number of equality atoms :   16 ( 139 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_201,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,k2_tmap_1(A,B,E,D)),k2_tmap_1(A,B,E,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(C,A)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(A,B,D,C))
            & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
            & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_162,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                         => ( ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),F,k2_tmap_1(A,B,E,C))
                              & m1_pre_topc(D,C) )
                           => r2_funct_2(u1_struct_0(D),u1_struct_0(B),k3_tmap_1(A,B,C,D,F),k2_tmap_1(A,B,E,D)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tmap_1)).

tff(f_34,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(c_44,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_30,plain,(
    ! [B_32,A_30] :
      ( r1_tarski(u1_struct_0(B_32),u1_struct_0(A_30))
      | ~ m1_pre_topc(B_32,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_40,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_24,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_115,plain,(
    ! [B_151,A_152,D_153,C_154] :
      ( k1_xboole_0 = B_151
      | v1_funct_2(k2_partfun1(A_152,B_151,D_153,C_154),C_154,B_151)
      | ~ r1_tarski(C_154,A_152)
      | ~ m1_subset_1(D_153,k1_zfmisc_1(k2_zfmisc_1(A_152,B_151)))
      | ~ v1_funct_2(D_153,A_152,B_151)
      | ~ v1_funct_1(D_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_121,plain,(
    ! [C_154] :
      ( u1_struct_0('#skF_2') = k1_xboole_0
      | v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',C_154),C_154,u1_struct_0('#skF_2'))
      | ~ r1_tarski(C_154,u1_struct_0('#skF_1'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_115])).

tff(c_126,plain,(
    ! [C_154] :
      ( u1_struct_0('#skF_2') = k1_xboole_0
      | v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',C_154),C_154,u1_struct_0('#skF_2'))
      | ~ r1_tarski(C_154,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_121])).

tff(c_127,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_26,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(u1_struct_0(A_14))
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_143,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_26])).

tff(c_149,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_143])).

tff(c_150,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_149])).

tff(c_154,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_150])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_154])).

tff(c_160,plain,(
    u1_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_216,plain,(
    ! [A_175,B_176,C_177,D_178] :
      ( k2_partfun1(u1_struct_0(A_175),u1_struct_0(B_176),C_177,u1_struct_0(D_178)) = k2_tmap_1(A_175,B_176,C_177,D_178)
      | ~ m1_pre_topc(D_178,A_175)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_175),u1_struct_0(B_176))))
      | ~ v1_funct_2(C_177,u1_struct_0(A_175),u1_struct_0(B_176))
      | ~ v1_funct_1(C_177)
      | ~ l1_pre_topc(B_176)
      | ~ v2_pre_topc(B_176)
      | v2_struct_0(B_176)
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_227,plain,(
    ! [D_178] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_178)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_178)
      | ~ m1_pre_topc(D_178,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_216])).

tff(c_233,plain,(
    ! [D_178] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_178)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_178)
      | ~ m1_pre_topc(D_178,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_42,c_40,c_227])).

tff(c_235,plain,(
    ! [D_179] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_179)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_179)
      | ~ m1_pre_topc(D_179,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_233])).

tff(c_14,plain,(
    ! [B_10,A_9,D_12,C_11] :
      ( k1_xboole_0 = B_10
      | m1_subset_1(k2_partfun1(A_9,B_10,D_12,C_11),k1_zfmisc_1(k2_zfmisc_1(C_11,B_10)))
      | ~ r1_tarski(C_11,A_9)
      | ~ m1_subset_1(D_12,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_2(D_12,A_9,B_10)
      | ~ v1_funct_1(D_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_244,plain,(
    ! [D_179] :
      ( u1_struct_0('#skF_2') = k1_xboole_0
      | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_179),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_179),u1_struct_0('#skF_2'))))
      | ~ r1_tarski(u1_struct_0(D_179),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_179,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_14])).

tff(c_260,plain,(
    ! [D_179] :
      ( u1_struct_0('#skF_2') = k1_xboole_0
      | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_179),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_179),u1_struct_0('#skF_2'))))
      | ~ r1_tarski(u1_struct_0(D_179),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(D_179,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_244])).

tff(c_295,plain,(
    ! [D_191] :
      ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_191),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_191),u1_struct_0('#skF_2'))))
      | ~ r1_tarski(u1_struct_0(D_191),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(D_191,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_260])).

tff(c_8,plain,(
    ! [A_5,B_6,D_8] :
      ( r2_funct_2(A_5,B_6,D_8,D_8)
      | ~ m1_subset_1(D_8,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(D_8,A_5,B_6)
      | ~ v1_funct_1(D_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_548,plain,(
    ! [D_233] :
      ( r2_funct_2(u1_struct_0(D_233),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_233),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_233))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_233),u1_struct_0(D_233),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_233))
      | ~ r1_tarski(u1_struct_0(D_233),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(D_233,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_295,c_8])).

tff(c_32,plain,(
    ! [C_81,D_89,F_95,A_33,B_65,E_93] :
      ( r2_funct_2(u1_struct_0(D_89),u1_struct_0(B_65),k3_tmap_1(A_33,B_65,C_81,D_89,F_95),k2_tmap_1(A_33,B_65,E_93,D_89))
      | ~ m1_pre_topc(D_89,C_81)
      | ~ r2_funct_2(u1_struct_0(C_81),u1_struct_0(B_65),F_95,k2_tmap_1(A_33,B_65,E_93,C_81))
      | ~ m1_subset_1(F_95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_81),u1_struct_0(B_65))))
      | ~ v1_funct_2(F_95,u1_struct_0(C_81),u1_struct_0(B_65))
      | ~ v1_funct_1(F_95)
      | ~ m1_subset_1(E_93,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_33),u1_struct_0(B_65))))
      | ~ v1_funct_2(E_93,u1_struct_0(A_33),u1_struct_0(B_65))
      | ~ v1_funct_1(E_93)
      | ~ m1_pre_topc(D_89,A_33)
      | v2_struct_0(D_89)
      | ~ m1_pre_topc(C_81,A_33)
      | v2_struct_0(C_81)
      | ~ l1_pre_topc(B_65)
      | ~ v2_pre_topc(B_65)
      | v2_struct_0(B_65)
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_550,plain,(
    ! [D_89,D_233] :
      ( r2_funct_2(u1_struct_0(D_89),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',D_233,D_89,k2_tmap_1('#skF_1','#skF_2','#skF_5',D_233)),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_89))
      | ~ m1_pre_topc(D_89,D_233)
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_233),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_233),u1_struct_0('#skF_2'))))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_89,'#skF_1')
      | v2_struct_0(D_89)
      | v2_struct_0(D_233)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_233),u1_struct_0(D_233),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_233))
      | ~ r1_tarski(u1_struct_0(D_233),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(D_233,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_548,c_32])).

tff(c_555,plain,(
    ! [D_89,D_233] :
      ( r2_funct_2(u1_struct_0(D_89),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',D_233,D_89,k2_tmap_1('#skF_1','#skF_2','#skF_5',D_233)),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_89))
      | ~ m1_pre_topc(D_89,D_233)
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_233),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_233),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(D_89,'#skF_1')
      | v2_struct_0(D_89)
      | v2_struct_0(D_233)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_233),u1_struct_0(D_233),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_233))
      | ~ r1_tarski(u1_struct_0(D_233),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(D_233,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_42,c_40,c_38,c_550])).

tff(c_658,plain,(
    ! [D_262,D_263] :
      ( r2_funct_2(u1_struct_0(D_262),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',D_263,D_262,k2_tmap_1('#skF_1','#skF_2','#skF_5',D_263)),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_262))
      | ~ m1_pre_topc(D_262,D_263)
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_263),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_263),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(D_262,'#skF_1')
      | v2_struct_0(D_262)
      | v2_struct_0(D_263)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_263),u1_struct_0(D_263),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_263))
      | ~ r1_tarski(u1_struct_0(D_263),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(D_263,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_555])).

tff(c_34,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_665,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_658,c_34])).

tff(c_673,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_36,c_665])).

tff(c_674,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_50,c_673])).

tff(c_675,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_674])).

tff(c_678,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_675])).

tff(c_682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_44,c_678])).

tff(c_684,plain,(
    r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_674])).

tff(c_159,plain,(
    ! [C_154] :
      ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',C_154),C_154,u1_struct_0('#skF_2'))
      | ~ r1_tarski(C_154,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_247,plain,(
    ! [D_179] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_179),u1_struct_0(D_179),u1_struct_0('#skF_2'))
      | ~ r1_tarski(u1_struct_0(D_179),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(D_179,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_159])).

tff(c_66,plain,(
    ! [A_126,B_127,C_128,D_129] :
      ( v1_funct_1(k2_partfun1(A_126,B_127,C_128,D_129))
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ v1_funct_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_68,plain,(
    ! [D_129] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',D_129))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_66])).

tff(c_71,plain,(
    ! [D_129] : v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',D_129)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_68])).

tff(c_254,plain,(
    ! [D_179] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_179))
      | ~ m1_pre_topc(D_179,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_71])).

tff(c_261,plain,(
    ! [D_179] :
      ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_179),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_179),u1_struct_0('#skF_2'))))
      | ~ r1_tarski(u1_struct_0(D_179),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(D_179,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_260])).

tff(c_683,plain,
    ( ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_674])).

tff(c_685,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_683])).

tff(c_688,plain,
    ( ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_261,c_685])).

tff(c_692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_684,c_688])).

tff(c_693,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_683])).

tff(c_721,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_693])).

tff(c_724,plain,(
    ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_254,c_721])).

tff(c_728,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_724])).

tff(c_729,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_693])).

tff(c_734,plain,
    ( ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_247,c_729])).

tff(c_738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_684,c_734])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.86/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.67  
% 3.86/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.67  %$ r2_funct_2 > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.86/1.67  
% 3.86/1.67  %Foreground sorts:
% 3.86/1.67  
% 3.86/1.67  
% 3.86/1.67  %Background operators:
% 3.86/1.67  
% 3.86/1.67  
% 3.86/1.67  %Foreground operators:
% 3.86/1.67  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.86/1.67  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.86/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.86/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.86/1.67  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.86/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.86/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.86/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.86/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.86/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.86/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.86/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.86/1.67  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.86/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.86/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.86/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.67  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.86/1.67  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.86/1.67  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.86/1.67  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.86/1.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.86/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.86/1.67  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.86/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.86/1.67  
% 3.86/1.70  tff(f_201, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, k2_tmap_1(A, B, E, D)), k2_tmap_1(A, B, E, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tmap_1)).
% 3.86/1.70  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 3.86/1.70  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.86/1.70  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.86/1.70  tff(f_69, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 3.86/1.70  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.86/1.70  tff(f_108, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.86/1.70  tff(f_50, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.86/1.70  tff(f_162, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(C), u1_struct_0(B), F, k2_tmap_1(A, B, E, C)) & m1_pre_topc(D, C)) => r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, C, D, F), k2_tmap_1(A, B, E, D))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tmap_1)).
% 3.86/1.70  tff(f_34, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 3.86/1.70  tff(c_44, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 3.86/1.70  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 3.86/1.70  tff(c_30, plain, (![B_32, A_30]: (r1_tarski(u1_struct_0(B_32), u1_struct_0(A_30)) | ~m1_pre_topc(B_32, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.86/1.70  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 3.86/1.70  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 3.86/1.70  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 3.86/1.70  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 3.86/1.70  tff(c_62, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 3.86/1.70  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 3.86/1.70  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 3.86/1.70  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 3.86/1.70  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 3.86/1.70  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_201])).
% 3.86/1.70  tff(c_40, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 3.86/1.70  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_201])).
% 3.86/1.70  tff(c_24, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.86/1.70  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.86/1.70  tff(c_115, plain, (![B_151, A_152, D_153, C_154]: (k1_xboole_0=B_151 | v1_funct_2(k2_partfun1(A_152, B_151, D_153, C_154), C_154, B_151) | ~r1_tarski(C_154, A_152) | ~m1_subset_1(D_153, k1_zfmisc_1(k2_zfmisc_1(A_152, B_151))) | ~v1_funct_2(D_153, A_152, B_151) | ~v1_funct_1(D_153))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.86/1.70  tff(c_121, plain, (![C_154]: (u1_struct_0('#skF_2')=k1_xboole_0 | v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', C_154), C_154, u1_struct_0('#skF_2')) | ~r1_tarski(C_154, u1_struct_0('#skF_1')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_115])).
% 3.86/1.70  tff(c_126, plain, (![C_154]: (u1_struct_0('#skF_2')=k1_xboole_0 | v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', C_154), C_154, u1_struct_0('#skF_2')) | ~r1_tarski(C_154, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_121])).
% 3.86/1.70  tff(c_127, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_126])).
% 3.86/1.70  tff(c_26, plain, (![A_14]: (~v1_xboole_0(u1_struct_0(A_14)) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.86/1.70  tff(c_143, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_127, c_26])).
% 3.86/1.70  tff(c_149, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_143])).
% 3.86/1.70  tff(c_150, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_149])).
% 3.86/1.70  tff(c_154, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_150])).
% 3.86/1.70  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_154])).
% 3.86/1.70  tff(c_160, plain, (u1_struct_0('#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_126])).
% 3.86/1.70  tff(c_216, plain, (![A_175, B_176, C_177, D_178]: (k2_partfun1(u1_struct_0(A_175), u1_struct_0(B_176), C_177, u1_struct_0(D_178))=k2_tmap_1(A_175, B_176, C_177, D_178) | ~m1_pre_topc(D_178, A_175) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_175), u1_struct_0(B_176)))) | ~v1_funct_2(C_177, u1_struct_0(A_175), u1_struct_0(B_176)) | ~v1_funct_1(C_177) | ~l1_pre_topc(B_176) | ~v2_pre_topc(B_176) | v2_struct_0(B_176) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.86/1.70  tff(c_227, plain, (![D_178]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_178))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_178) | ~m1_pre_topc(D_178, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_216])).
% 3.86/1.70  tff(c_233, plain, (![D_178]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_178))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_178) | ~m1_pre_topc(D_178, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_42, c_40, c_227])).
% 3.86/1.70  tff(c_235, plain, (![D_179]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_179))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_179) | ~m1_pre_topc(D_179, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_233])).
% 3.86/1.70  tff(c_14, plain, (![B_10, A_9, D_12, C_11]: (k1_xboole_0=B_10 | m1_subset_1(k2_partfun1(A_9, B_10, D_12, C_11), k1_zfmisc_1(k2_zfmisc_1(C_11, B_10))) | ~r1_tarski(C_11, A_9) | ~m1_subset_1(D_12, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | ~v1_funct_2(D_12, A_9, B_10) | ~v1_funct_1(D_12))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.86/1.70  tff(c_244, plain, (![D_179]: (u1_struct_0('#skF_2')=k1_xboole_0 | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_179), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_179), u1_struct_0('#skF_2')))) | ~r1_tarski(u1_struct_0(D_179), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_179, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_235, c_14])).
% 3.86/1.70  tff(c_260, plain, (![D_179]: (u1_struct_0('#skF_2')=k1_xboole_0 | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_179), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_179), u1_struct_0('#skF_2')))) | ~r1_tarski(u1_struct_0(D_179), u1_struct_0('#skF_1')) | ~m1_pre_topc(D_179, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_244])).
% 3.86/1.70  tff(c_295, plain, (![D_191]: (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_191), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_191), u1_struct_0('#skF_2')))) | ~r1_tarski(u1_struct_0(D_191), u1_struct_0('#skF_1')) | ~m1_pre_topc(D_191, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_160, c_260])).
% 3.86/1.70  tff(c_8, plain, (![A_5, B_6, D_8]: (r2_funct_2(A_5, B_6, D_8, D_8) | ~m1_subset_1(D_8, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(D_8, A_5, B_6) | ~v1_funct_1(D_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.86/1.70  tff(c_548, plain, (![D_233]: (r2_funct_2(u1_struct_0(D_233), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_233), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_233)) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_233), u1_struct_0(D_233), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_233)) | ~r1_tarski(u1_struct_0(D_233), u1_struct_0('#skF_1')) | ~m1_pre_topc(D_233, '#skF_1'))), inference(resolution, [status(thm)], [c_295, c_8])).
% 3.86/1.70  tff(c_32, plain, (![C_81, D_89, F_95, A_33, B_65, E_93]: (r2_funct_2(u1_struct_0(D_89), u1_struct_0(B_65), k3_tmap_1(A_33, B_65, C_81, D_89, F_95), k2_tmap_1(A_33, B_65, E_93, D_89)) | ~m1_pre_topc(D_89, C_81) | ~r2_funct_2(u1_struct_0(C_81), u1_struct_0(B_65), F_95, k2_tmap_1(A_33, B_65, E_93, C_81)) | ~m1_subset_1(F_95, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_81), u1_struct_0(B_65)))) | ~v1_funct_2(F_95, u1_struct_0(C_81), u1_struct_0(B_65)) | ~v1_funct_1(F_95) | ~m1_subset_1(E_93, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_33), u1_struct_0(B_65)))) | ~v1_funct_2(E_93, u1_struct_0(A_33), u1_struct_0(B_65)) | ~v1_funct_1(E_93) | ~m1_pre_topc(D_89, A_33) | v2_struct_0(D_89) | ~m1_pre_topc(C_81, A_33) | v2_struct_0(C_81) | ~l1_pre_topc(B_65) | ~v2_pre_topc(B_65) | v2_struct_0(B_65) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.86/1.70  tff(c_550, plain, (![D_89, D_233]: (r2_funct_2(u1_struct_0(D_89), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', D_233, D_89, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_233)), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_89)) | ~m1_pre_topc(D_89, D_233) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_233), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_233), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_89, '#skF_1') | v2_struct_0(D_89) | v2_struct_0(D_233) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_233), u1_struct_0(D_233), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_233)) | ~r1_tarski(u1_struct_0(D_233), u1_struct_0('#skF_1')) | ~m1_pre_topc(D_233, '#skF_1'))), inference(resolution, [status(thm)], [c_548, c_32])).
% 3.86/1.70  tff(c_555, plain, (![D_89, D_233]: (r2_funct_2(u1_struct_0(D_89), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', D_233, D_89, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_233)), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_89)) | ~m1_pre_topc(D_89, D_233) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_233), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_233), u1_struct_0('#skF_2')))) | ~m1_pre_topc(D_89, '#skF_1') | v2_struct_0(D_89) | v2_struct_0(D_233) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_233), u1_struct_0(D_233), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_233)) | ~r1_tarski(u1_struct_0(D_233), u1_struct_0('#skF_1')) | ~m1_pre_topc(D_233, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_42, c_40, c_38, c_550])).
% 3.86/1.70  tff(c_658, plain, (![D_262, D_263]: (r2_funct_2(u1_struct_0(D_262), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', D_263, D_262, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_263)), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_262)) | ~m1_pre_topc(D_262, D_263) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_263), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_263), u1_struct_0('#skF_2')))) | ~m1_pre_topc(D_262, '#skF_1') | v2_struct_0(D_262) | v2_struct_0(D_263) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_263), u1_struct_0(D_263), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_263)) | ~r1_tarski(u1_struct_0(D_263), u1_struct_0('#skF_1')) | ~m1_pre_topc(D_263, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_555])).
% 3.86/1.70  tff(c_34, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 3.86/1.70  tff(c_665, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~m1_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_658, c_34])).
% 3.86/1.70  tff(c_673, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48, c_36, c_665])).
% 3.86/1.70  tff(c_674, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_46, c_50, c_673])).
% 3.86/1.70  tff(c_675, plain, (~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_674])).
% 3.86/1.70  tff(c_678, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_675])).
% 3.86/1.70  tff(c_682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_44, c_678])).
% 3.86/1.70  tff(c_684, plain, (r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_674])).
% 3.86/1.70  tff(c_159, plain, (![C_154]: (v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', C_154), C_154, u1_struct_0('#skF_2')) | ~r1_tarski(C_154, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_126])).
% 3.86/1.70  tff(c_247, plain, (![D_179]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_179), u1_struct_0(D_179), u1_struct_0('#skF_2')) | ~r1_tarski(u1_struct_0(D_179), u1_struct_0('#skF_1')) | ~m1_pre_topc(D_179, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_235, c_159])).
% 3.86/1.70  tff(c_66, plain, (![A_126, B_127, C_128, D_129]: (v1_funct_1(k2_partfun1(A_126, B_127, C_128, D_129)) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~v1_funct_1(C_128))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.86/1.70  tff(c_68, plain, (![D_129]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', D_129)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_66])).
% 3.86/1.70  tff(c_71, plain, (![D_129]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', D_129)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_68])).
% 3.86/1.70  tff(c_254, plain, (![D_179]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_179)) | ~m1_pre_topc(D_179, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_235, c_71])).
% 3.86/1.70  tff(c_261, plain, (![D_179]: (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_179), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_179), u1_struct_0('#skF_2')))) | ~r1_tarski(u1_struct_0(D_179), u1_struct_0('#skF_1')) | ~m1_pre_topc(D_179, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_160, c_260])).
% 3.86/1.70  tff(c_683, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_674])).
% 3.86/1.70  tff(c_685, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_683])).
% 3.86/1.70  tff(c_688, plain, (~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~m1_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_261, c_685])).
% 3.86/1.70  tff(c_692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_684, c_688])).
% 3.86/1.70  tff(c_693, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_683])).
% 3.86/1.70  tff(c_721, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_693])).
% 3.86/1.70  tff(c_724, plain, (~m1_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_254, c_721])).
% 3.86/1.70  tff(c_728, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_724])).
% 3.86/1.70  tff(c_729, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_693])).
% 3.86/1.70  tff(c_734, plain, (~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~m1_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_247, c_729])).
% 3.86/1.70  tff(c_738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_684, c_734])).
% 3.86/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.70  
% 3.86/1.70  Inference rules
% 3.86/1.70  ----------------------
% 3.86/1.70  #Ref     : 0
% 3.86/1.70  #Sup     : 141
% 3.86/1.70  #Fact    : 0
% 3.86/1.70  #Define  : 0
% 3.86/1.70  #Split   : 6
% 3.86/1.70  #Chain   : 0
% 3.86/1.70  #Close   : 0
% 3.86/1.70  
% 3.86/1.70  Ordering : KBO
% 3.86/1.70  
% 3.86/1.70  Simplification rules
% 3.86/1.70  ----------------------
% 3.86/1.70  #Subsume      : 29
% 3.86/1.70  #Demod        : 141
% 4.20/1.70  #Tautology    : 16
% 4.20/1.70  #SimpNegUnit  : 38
% 4.20/1.70  #BackRed      : 6
% 4.20/1.70  
% 4.20/1.70  #Partial instantiations: 0
% 4.20/1.70  #Strategies tried      : 1
% 4.20/1.70  
% 4.20/1.70  Timing (in seconds)
% 4.20/1.70  ----------------------
% 4.20/1.70  Preprocessing        : 0.38
% 4.20/1.70  Parsing              : 0.21
% 4.20/1.70  CNF conversion       : 0.04
% 4.20/1.70  Main loop            : 0.54
% 4.20/1.70  Inferencing          : 0.20
% 4.20/1.70  Reduction            : 0.17
% 4.20/1.70  Demodulation         : 0.12
% 4.20/1.70  BG Simplification    : 0.03
% 4.20/1.70  Subsumption          : 0.12
% 4.20/1.70  Abstraction          : 0.03
% 4.20/1.70  MUC search           : 0.00
% 4.20/1.70  Cooper               : 0.00
% 4.20/1.70  Total                : 0.97
% 4.20/1.70  Index Insertion      : 0.00
% 4.20/1.70  Index Deletion       : 0.00
% 4.20/1.70  Index Matching       : 0.00
% 4.20/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
