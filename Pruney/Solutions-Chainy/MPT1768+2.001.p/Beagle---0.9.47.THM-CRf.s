%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:16 EST 2020

% Result     : Theorem 7.45s
% Output     : CNFRefutation 7.82s
% Verified   : 
% Statistics : Number of formulae       :  146 (2552 expanded)
%              Number of leaves         :   40 (1004 expanded)
%              Depth                    :   24
%              Number of atoms          :  450 (20511 expanded)
%              Number of equality atoms :   41 ( 576 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_244,negated_conjecture,(
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
                        ( ( ~ v2_struct_0(E)
                          & m1_pre_topc(E,A) )
                       => ( ( m1_pre_topc(D,C)
                            & m1_pre_topc(E,D) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                             => r2_funct_2(u1_struct_0(E),u1_struct_0(B),k3_tmap_1(A,B,D,E,k3_tmap_1(A,B,C,D,F)),k3_tmap_1(A,B,C,E,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tmap_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_197,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,B)
             => m1_pre_topc(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

tff(f_140,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_34,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_147,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_53,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_185,axiom,(
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
                     => ( m1_pre_topc(C,D)
                       => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,k2_tmap_1(A,B,E,D)),k2_tmap_1(A,B,E,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tmap_1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_70,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_68,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_58,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_106,plain,(
    ! [B_165,A_166] :
      ( v2_pre_topc(B_165)
      | ~ m1_pre_topc(B_165,A_166)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_121,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_106])).

tff(c_136,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_121])).

tff(c_74,plain,(
    ! [B_162,A_163] :
      ( l1_pre_topc(B_162)
      | ~ m1_pre_topc(B_162,A_163)
      | ~ l1_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_89,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_74])).

tff(c_100,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_89])).

tff(c_48,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_46,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_142,plain,(
    ! [C_169,A_170,B_171] :
      ( m1_pre_topc(C_169,A_170)
      | ~ m1_pre_topc(C_169,B_171)
      | ~ m1_pre_topc(B_171,A_170)
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_153,plain,(
    ! [A_170] :
      ( m1_pre_topc('#skF_5',A_170)
      | ~ m1_pre_topc('#skF_4',A_170)
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170) ) ),
    inference(resolution,[status(thm)],[c_46,c_142])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_50,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_64,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_62,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_42,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_557,plain,(
    ! [C_233,A_234,D_237,E_236,B_235] :
      ( k3_tmap_1(A_234,B_235,C_233,D_237,E_236) = k2_partfun1(u1_struct_0(C_233),u1_struct_0(B_235),E_236,u1_struct_0(D_237))
      | ~ m1_pre_topc(D_237,C_233)
      | ~ m1_subset_1(E_236,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_233),u1_struct_0(B_235))))
      | ~ v1_funct_2(E_236,u1_struct_0(C_233),u1_struct_0(B_235))
      | ~ v1_funct_1(E_236)
      | ~ m1_pre_topc(D_237,A_234)
      | ~ m1_pre_topc(C_233,A_234)
      | ~ l1_pre_topc(B_235)
      | ~ v2_pre_topc(B_235)
      | v2_struct_0(B_235)
      | ~ l1_pre_topc(A_234)
      | ~ v2_pre_topc(A_234)
      | v2_struct_0(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_572,plain,(
    ! [A_234,D_237] :
      ( k3_tmap_1(A_234,'#skF_2','#skF_3',D_237,'#skF_6') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_237))
      | ~ m1_pre_topc(D_237,'#skF_3')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_237,A_234)
      | ~ m1_pre_topc('#skF_3',A_234)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_234)
      | ~ v2_pre_topc(A_234)
      | v2_struct_0(A_234) ) ),
    inference(resolution,[status(thm)],[c_40,c_557])).

tff(c_586,plain,(
    ! [A_234,D_237] :
      ( k3_tmap_1(A_234,'#skF_2','#skF_3',D_237,'#skF_6') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_237))
      | ~ m1_pre_topc(D_237,'#skF_3')
      | ~ m1_pre_topc(D_237,A_234)
      | ~ m1_pre_topc('#skF_3',A_234)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_234)
      | ~ v2_pre_topc(A_234)
      | v2_struct_0(A_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_44,c_42,c_572])).

tff(c_588,plain,(
    ! [A_238,D_239] :
      ( k3_tmap_1(A_238,'#skF_2','#skF_3',D_239,'#skF_6') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_239))
      | ~ m1_pre_topc(D_239,'#skF_3')
      | ~ m1_pre_topc(D_239,A_238)
      | ~ m1_pre_topc('#skF_3',A_238)
      | ~ l1_pre_topc(A_238)
      | ~ v2_pre_topc(A_238)
      | v2_struct_0(A_238) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_586])).

tff(c_600,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_588])).

tff(c_618,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_600])).

tff(c_619,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_618])).

tff(c_660,plain,(
    ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_619])).

tff(c_666,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_153,c_660])).

tff(c_673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_100,c_48,c_666])).

tff(c_675,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_619])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_54,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_602,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_588])).

tff(c_622,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_48,c_602])).

tff(c_623,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_622])).

tff(c_448,plain,(
    ! [A_218,B_219,C_220,D_221] :
      ( k2_partfun1(u1_struct_0(A_218),u1_struct_0(B_219),C_220,u1_struct_0(D_221)) = k2_tmap_1(A_218,B_219,C_220,D_221)
      | ~ m1_pre_topc(D_221,A_218)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_218),u1_struct_0(B_219))))
      | ~ v1_funct_2(C_220,u1_struct_0(A_218),u1_struct_0(B_219))
      | ~ v1_funct_1(C_220)
      | ~ l1_pre_topc(B_219)
      | ~ v2_pre_topc(B_219)
      | v2_struct_0(B_219)
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218)
      | v2_struct_0(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_459,plain,(
    ! [D_221] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_221)) = k2_tmap_1('#skF_3','#skF_2','#skF_6',D_221)
      | ~ m1_pre_topc(D_221,'#skF_3')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_448])).

tff(c_465,plain,(
    ! [D_221] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_221)) = k2_tmap_1('#skF_3','#skF_2','#skF_6',D_221)
      | ~ m1_pre_topc(D_221,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_100,c_64,c_62,c_44,c_42,c_459])).

tff(c_466,plain,(
    ! [D_221] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_221)) = k2_tmap_1('#skF_3','#skF_2','#skF_6',D_221)
      | ~ m1_pre_topc(D_221,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_66,c_465])).

tff(c_631,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_466])).

tff(c_651,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_631])).

tff(c_158,plain,(
    ! [A_172,B_173,C_174,D_175] :
      ( v1_funct_1(k2_partfun1(A_172,B_173,C_174,D_175))
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173)))
      | ~ v1_funct_1(C_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_160,plain,(
    ! [D_175] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',D_175))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_158])).

tff(c_163,plain,(
    ! [D_175] : v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',D_175)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_160])).

tff(c_644,plain,(
    v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_163])).

tff(c_746,plain,(
    v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_644])).

tff(c_32,plain,(
    ! [B_65,A_63] :
      ( r1_tarski(u1_struct_0(B_65),u1_struct_0(A_63))
      | ~ m1_pre_topc(B_65,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_747,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_623])).

tff(c_22,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_375,plain,(
    ! [B_205,A_206,D_207,C_208] :
      ( k1_xboole_0 = B_205
      | v1_funct_2(k2_partfun1(A_206,B_205,D_207,C_208),C_208,B_205)
      | ~ r1_tarski(C_208,A_206)
      | ~ m1_subset_1(D_207,k1_zfmisc_1(k2_zfmisc_1(A_206,B_205)))
      | ~ v1_funct_2(D_207,A_206,B_205)
      | ~ v1_funct_1(D_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_381,plain,(
    ! [C_208] :
      ( u1_struct_0('#skF_2') = k1_xboole_0
      | v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',C_208),C_208,u1_struct_0('#skF_2'))
      | ~ r1_tarski(C_208,u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_375])).

tff(c_386,plain,(
    ! [C_208] :
      ( u1_struct_0('#skF_2') = k1_xboole_0
      | v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',C_208),C_208,u1_struct_0('#skF_2'))
      | ~ r1_tarski(C_208,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_381])).

tff(c_387,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_386])).

tff(c_26,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_402,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_26])).

tff(c_408,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_402])).

tff(c_409,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_408])).

tff(c_413,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_409])).

tff(c_417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_413])).

tff(c_418,plain,(
    ! [C_208] :
      ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',C_208),C_208,u1_struct_0('#skF_2'))
      | ~ r1_tarski(C_208,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_764,plain,
    ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_747,c_418])).

tff(c_985,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_764])).

tff(c_989,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_985])).

tff(c_993,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_48,c_989])).

tff(c_994,plain,(
    v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_764])).

tff(c_995,plain,(
    r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_764])).

tff(c_419,plain,(
    u1_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_10,plain,(
    ! [B_6,A_5,D_8,C_7] :
      ( k1_xboole_0 = B_6
      | m1_subset_1(k2_partfun1(A_5,B_6,D_8,C_7),k1_zfmisc_1(k2_zfmisc_1(C_7,B_6)))
      | ~ r1_tarski(C_7,A_5)
      | ~ m1_subset_1(D_8,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(D_8,A_5,B_6)
      | ~ v1_funct_1(D_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_761,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_747,c_10])).

tff(c_781,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_761])).

tff(c_782,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_419,c_781])).

tff(c_1102,plain,(
    m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_995,c_782])).

tff(c_30,plain,(
    ! [C_56,E_62,A_32,D_60,B_48] :
      ( k3_tmap_1(A_32,B_48,C_56,D_60,E_62) = k2_partfun1(u1_struct_0(C_56),u1_struct_0(B_48),E_62,u1_struct_0(D_60))
      | ~ m1_pre_topc(D_60,C_56)
      | ~ m1_subset_1(E_62,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_56),u1_struct_0(B_48))))
      | ~ v1_funct_2(E_62,u1_struct_0(C_56),u1_struct_0(B_48))
      | ~ v1_funct_1(E_62)
      | ~ m1_pre_topc(D_60,A_32)
      | ~ m1_pre_topc(C_56,A_32)
      | ~ l1_pre_topc(B_48)
      | ~ v2_pre_topc(B_48)
      | v2_struct_0(B_48)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1106,plain,(
    ! [A_32,D_60] :
      ( k3_tmap_1(A_32,'#skF_2','#skF_4',D_60,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_60))
      | ~ m1_pre_topc(D_60,'#skF_4')
      | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'))
      | ~ m1_pre_topc(D_60,A_32)
      | ~ m1_pre_topc('#skF_4',A_32)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_1102,c_30])).

tff(c_1121,plain,(
    ! [A_32,D_60] :
      ( k3_tmap_1(A_32,'#skF_2','#skF_4',D_60,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_60))
      | ~ m1_pre_topc(D_60,'#skF_4')
      | ~ m1_pre_topc(D_60,A_32)
      | ~ m1_pre_topc('#skF_4',A_32)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_746,c_994,c_1106])).

tff(c_2272,plain,(
    ! [A_360,D_361] :
      ( k3_tmap_1(A_360,'#skF_2','#skF_4',D_361,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_361))
      | ~ m1_pre_topc(D_361,'#skF_4')
      | ~ m1_pre_topc(D_361,A_360)
      | ~ m1_pre_topc('#skF_4',A_360)
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360)
      | v2_struct_0(A_360) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1121])).

tff(c_118,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_106])).

tff(c_133,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_118])).

tff(c_86,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_74])).

tff(c_97,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_86])).

tff(c_28,plain,(
    ! [A_17,B_25,C_29,D_31] :
      ( k2_partfun1(u1_struct_0(A_17),u1_struct_0(B_25),C_29,u1_struct_0(D_31)) = k2_tmap_1(A_17,B_25,C_29,D_31)
      | ~ m1_pre_topc(D_31,A_17)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_17),u1_struct_0(B_25))))
      | ~ v1_funct_2(C_29,u1_struct_0(A_17),u1_struct_0(B_25))
      | ~ v1_funct_1(C_29)
      | ~ l1_pre_topc(B_25)
      | ~ v2_pre_topc(B_25)
      | v2_struct_0(B_25)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1108,plain,(
    ! [D_31] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_31)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_31)
      | ~ m1_pre_topc(D_31,'#skF_4')
      | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1102,c_28])).

tff(c_1125,plain,(
    ! [D_31] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_31)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_31)
      | ~ m1_pre_topc(D_31,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_97,c_64,c_62,c_746,c_994,c_1108])).

tff(c_1126,plain,(
    ! [D_31] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_31)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_31)
      | ~ m1_pre_topc(D_31,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_66,c_1125])).

tff(c_3036,plain,(
    ! [A_412,D_413] :
      ( k3_tmap_1(A_412,'#skF_2','#skF_4',D_413,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_413)
      | ~ m1_pre_topc(D_413,'#skF_4')
      | ~ m1_pre_topc(D_413,'#skF_4')
      | ~ m1_pre_topc(D_413,A_412)
      | ~ m1_pre_topc('#skF_4',A_412)
      | ~ l1_pre_topc(A_412)
      | ~ v2_pre_topc(A_412)
      | v2_struct_0(A_412) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2272,c_1126])).

tff(c_34,plain,(
    ! [A_66,B_82,E_96,D_94,C_90] :
      ( r2_funct_2(u1_struct_0(C_90),u1_struct_0(B_82),k3_tmap_1(A_66,B_82,D_94,C_90,k2_tmap_1(A_66,B_82,E_96,D_94)),k2_tmap_1(A_66,B_82,E_96,C_90))
      | ~ m1_pre_topc(C_90,D_94)
      | ~ m1_subset_1(E_96,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_66),u1_struct_0(B_82))))
      | ~ v1_funct_2(E_96,u1_struct_0(A_66),u1_struct_0(B_82))
      | ~ v1_funct_1(E_96)
      | ~ m1_pre_topc(D_94,A_66)
      | v2_struct_0(D_94)
      | ~ m1_pre_topc(C_90,A_66)
      | v2_struct_0(C_90)
      | ~ l1_pre_topc(B_82)
      | ~ v2_pre_topc(B_82)
      | v2_struct_0(B_82)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_3064,plain,(
    ! [D_413] :
      ( r2_funct_2(u1_struct_0(D_413),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_413),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_413))
      | ~ m1_pre_topc(D_413,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(D_413,'#skF_3')
      | v2_struct_0(D_413)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(D_413,'#skF_4')
      | ~ m1_pre_topc(D_413,'#skF_4')
      | ~ m1_pre_topc(D_413,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3036,c_34])).

tff(c_3076,plain,(
    ! [D_413] :
      ( r2_funct_2(u1_struct_0(D_413),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_413),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_413))
      | v2_struct_0('#skF_4')
      | v2_struct_0(D_413)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_413,'#skF_4')
      | ~ m1_pre_topc(D_413,'#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_100,c_48,c_136,c_100,c_64,c_62,c_48,c_44,c_42,c_40,c_3064])).

tff(c_3079,plain,(
    ! [D_414] :
      ( r2_funct_2(u1_struct_0(D_414),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_414),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_414))
      | v2_struct_0(D_414)
      | ~ m1_pre_topc(D_414,'#skF_4')
      | ~ m1_pre_topc(D_414,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_66,c_56,c_3076])).

tff(c_674,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_619])).

tff(c_869,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_674,c_466])).

tff(c_889,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_869])).

tff(c_38,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')),k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_748,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')),k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_38])).

tff(c_1205,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_748])).

tff(c_3060,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),'#skF_5'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3036,c_1205])).

tff(c_3073,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),'#skF_5'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_50,c_46,c_46,c_3060])).

tff(c_3074,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),'#skF_5'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3073])).

tff(c_3082,plain,
    ( v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_3079,c_3074])).

tff(c_3085,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_46,c_3082])).

tff(c_3087,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3085])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:45:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.45/2.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.45/2.58  
% 7.45/2.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.45/2.58  %$ r2_funct_2 > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.45/2.58  
% 7.45/2.58  %Foreground sorts:
% 7.45/2.58  
% 7.45/2.58  
% 7.45/2.58  %Background operators:
% 7.45/2.58  
% 7.45/2.58  
% 7.45/2.58  %Foreground operators:
% 7.45/2.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.45/2.58  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.45/2.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.45/2.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.45/2.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.45/2.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.45/2.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.45/2.58  tff('#skF_5', type, '#skF_5': $i).
% 7.45/2.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.45/2.58  tff('#skF_6', type, '#skF_6': $i).
% 7.45/2.58  tff('#skF_2', type, '#skF_2': $i).
% 7.45/2.58  tff('#skF_3', type, '#skF_3': $i).
% 7.45/2.58  tff('#skF_1', type, '#skF_1': $i).
% 7.45/2.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.45/2.58  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.45/2.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.45/2.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.45/2.58  tff('#skF_4', type, '#skF_4': $i).
% 7.45/2.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.45/2.58  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.45/2.58  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.45/2.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.45/2.58  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 7.45/2.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.45/2.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.45/2.58  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 7.45/2.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.45/2.58  
% 7.82/2.61  tff(f_244, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(D, C) & m1_pre_topc(E, D)) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(E), u1_struct_0(B), k3_tmap_1(A, B, D, E, k3_tmap_1(A, B, C, D, F)), k3_tmap_1(A, B, C, E, F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tmap_1)).
% 7.82/2.61  tff(f_62, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 7.82/2.61  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.82/2.61  tff(f_197, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, B) => m1_pre_topc(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 7.82/2.61  tff(f_140, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 7.82/2.61  tff(f_108, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 7.82/2.61  tff(f_34, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 7.82/2.61  tff(f_147, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 7.82/2.61  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.82/2.61  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.82/2.61  tff(f_53, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 7.82/2.61  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 7.82/2.61  tff(f_185, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, k2_tmap_1(A, B, E, D)), k2_tmap_1(A, B, E, C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tmap_1)).
% 7.82/2.61  tff(c_52, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.82/2.61  tff(c_70, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.82/2.61  tff(c_68, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.82/2.61  tff(c_58, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.82/2.61  tff(c_106, plain, (![B_165, A_166]: (v2_pre_topc(B_165) | ~m1_pre_topc(B_165, A_166) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.82/2.61  tff(c_121, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_106])).
% 7.82/2.61  tff(c_136, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_121])).
% 7.82/2.61  tff(c_74, plain, (![B_162, A_163]: (l1_pre_topc(B_162) | ~m1_pre_topc(B_162, A_163) | ~l1_pre_topc(A_163))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.82/2.61  tff(c_89, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_74])).
% 7.82/2.61  tff(c_100, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_89])).
% 7.82/2.61  tff(c_48, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.82/2.61  tff(c_46, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.82/2.61  tff(c_142, plain, (![C_169, A_170, B_171]: (m1_pre_topc(C_169, A_170) | ~m1_pre_topc(C_169, B_171) | ~m1_pre_topc(B_171, A_170) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170))), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.82/2.61  tff(c_153, plain, (![A_170]: (m1_pre_topc('#skF_5', A_170) | ~m1_pre_topc('#skF_4', A_170) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170))), inference(resolution, [status(thm)], [c_46, c_142])).
% 7.82/2.61  tff(c_72, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.82/2.61  tff(c_50, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.82/2.61  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.82/2.61  tff(c_64, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.82/2.61  tff(c_62, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.82/2.61  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.82/2.61  tff(c_42, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.82/2.61  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.82/2.61  tff(c_557, plain, (![C_233, A_234, D_237, E_236, B_235]: (k3_tmap_1(A_234, B_235, C_233, D_237, E_236)=k2_partfun1(u1_struct_0(C_233), u1_struct_0(B_235), E_236, u1_struct_0(D_237)) | ~m1_pre_topc(D_237, C_233) | ~m1_subset_1(E_236, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_233), u1_struct_0(B_235)))) | ~v1_funct_2(E_236, u1_struct_0(C_233), u1_struct_0(B_235)) | ~v1_funct_1(E_236) | ~m1_pre_topc(D_237, A_234) | ~m1_pre_topc(C_233, A_234) | ~l1_pre_topc(B_235) | ~v2_pre_topc(B_235) | v2_struct_0(B_235) | ~l1_pre_topc(A_234) | ~v2_pre_topc(A_234) | v2_struct_0(A_234))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.82/2.61  tff(c_572, plain, (![A_234, D_237]: (k3_tmap_1(A_234, '#skF_2', '#skF_3', D_237, '#skF_6')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_237)) | ~m1_pre_topc(D_237, '#skF_3') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_237, A_234) | ~m1_pre_topc('#skF_3', A_234) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_234) | ~v2_pre_topc(A_234) | v2_struct_0(A_234))), inference(resolution, [status(thm)], [c_40, c_557])).
% 7.82/2.61  tff(c_586, plain, (![A_234, D_237]: (k3_tmap_1(A_234, '#skF_2', '#skF_3', D_237, '#skF_6')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_237)) | ~m1_pre_topc(D_237, '#skF_3') | ~m1_pre_topc(D_237, A_234) | ~m1_pre_topc('#skF_3', A_234) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_234) | ~v2_pre_topc(A_234) | v2_struct_0(A_234))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_44, c_42, c_572])).
% 7.82/2.61  tff(c_588, plain, (![A_238, D_239]: (k3_tmap_1(A_238, '#skF_2', '#skF_3', D_239, '#skF_6')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_239)) | ~m1_pre_topc(D_239, '#skF_3') | ~m1_pre_topc(D_239, A_238) | ~m1_pre_topc('#skF_3', A_238) | ~l1_pre_topc(A_238) | ~v2_pre_topc(A_238) | v2_struct_0(A_238))), inference(negUnitSimplification, [status(thm)], [c_66, c_586])).
% 7.82/2.61  tff(c_600, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_588])).
% 7.82/2.61  tff(c_618, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_600])).
% 7.82/2.61  tff(c_619, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_72, c_618])).
% 7.82/2.61  tff(c_660, plain, (~m1_pre_topc('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_619])).
% 7.82/2.61  tff(c_666, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_153, c_660])).
% 7.82/2.61  tff(c_673, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_100, c_48, c_666])).
% 7.82/2.61  tff(c_675, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_619])).
% 7.82/2.61  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.82/2.61  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.82/2.61  tff(c_54, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.82/2.61  tff(c_602, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_588])).
% 7.82/2.61  tff(c_622, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_48, c_602])).
% 7.82/2.61  tff(c_623, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_72, c_622])).
% 7.82/2.61  tff(c_448, plain, (![A_218, B_219, C_220, D_221]: (k2_partfun1(u1_struct_0(A_218), u1_struct_0(B_219), C_220, u1_struct_0(D_221))=k2_tmap_1(A_218, B_219, C_220, D_221) | ~m1_pre_topc(D_221, A_218) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_218), u1_struct_0(B_219)))) | ~v1_funct_2(C_220, u1_struct_0(A_218), u1_struct_0(B_219)) | ~v1_funct_1(C_220) | ~l1_pre_topc(B_219) | ~v2_pre_topc(B_219) | v2_struct_0(B_219) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218) | v2_struct_0(A_218))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.82/2.61  tff(c_459, plain, (![D_221]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_221))=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_221) | ~m1_pre_topc(D_221, '#skF_3') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_448])).
% 7.82/2.61  tff(c_465, plain, (![D_221]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_221))=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_221) | ~m1_pre_topc(D_221, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_100, c_64, c_62, c_44, c_42, c_459])).
% 7.82/2.61  tff(c_466, plain, (![D_221]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_221))=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_221) | ~m1_pre_topc(D_221, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_66, c_465])).
% 7.82/2.61  tff(c_631, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_623, c_466])).
% 7.82/2.61  tff(c_651, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_631])).
% 7.82/2.61  tff(c_158, plain, (![A_172, B_173, C_174, D_175]: (v1_funct_1(k2_partfun1(A_172, B_173, C_174, D_175)) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))) | ~v1_funct_1(C_174))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.82/2.61  tff(c_160, plain, (![D_175]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', D_175)) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_158])).
% 7.82/2.61  tff(c_163, plain, (![D_175]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', D_175)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_160])).
% 7.82/2.61  tff(c_644, plain, (v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_623, c_163])).
% 7.82/2.61  tff(c_746, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_651, c_644])).
% 7.82/2.61  tff(c_32, plain, (![B_65, A_63]: (r1_tarski(u1_struct_0(B_65), u1_struct_0(A_63)) | ~m1_pre_topc(B_65, A_63) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.82/2.61  tff(c_747, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_651, c_623])).
% 7.82/2.61  tff(c_22, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.82/2.61  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.82/2.61  tff(c_375, plain, (![B_205, A_206, D_207, C_208]: (k1_xboole_0=B_205 | v1_funct_2(k2_partfun1(A_206, B_205, D_207, C_208), C_208, B_205) | ~r1_tarski(C_208, A_206) | ~m1_subset_1(D_207, k1_zfmisc_1(k2_zfmisc_1(A_206, B_205))) | ~v1_funct_2(D_207, A_206, B_205) | ~v1_funct_1(D_207))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.82/2.61  tff(c_381, plain, (![C_208]: (u1_struct_0('#skF_2')=k1_xboole_0 | v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', C_208), C_208, u1_struct_0('#skF_2')) | ~r1_tarski(C_208, u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_375])).
% 7.82/2.61  tff(c_386, plain, (![C_208]: (u1_struct_0('#skF_2')=k1_xboole_0 | v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', C_208), C_208, u1_struct_0('#skF_2')) | ~r1_tarski(C_208, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_381])).
% 7.82/2.61  tff(c_387, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_386])).
% 7.82/2.61  tff(c_26, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.82/2.61  tff(c_402, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_387, c_26])).
% 7.82/2.61  tff(c_408, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_402])).
% 7.82/2.61  tff(c_409, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_66, c_408])).
% 7.82/2.61  tff(c_413, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_409])).
% 7.82/2.61  tff(c_417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_413])).
% 7.82/2.61  tff(c_418, plain, (![C_208]: (v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', C_208), C_208, u1_struct_0('#skF_2')) | ~r1_tarski(C_208, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_386])).
% 7.82/2.61  tff(c_764, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_747, c_418])).
% 7.82/2.61  tff(c_985, plain, (~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_764])).
% 7.82/2.61  tff(c_989, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_985])).
% 7.82/2.61  tff(c_993, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_48, c_989])).
% 7.82/2.61  tff(c_994, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_764])).
% 7.82/2.61  tff(c_995, plain, (r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_764])).
% 7.82/2.61  tff(c_419, plain, (u1_struct_0('#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_386])).
% 7.82/2.61  tff(c_10, plain, (![B_6, A_5, D_8, C_7]: (k1_xboole_0=B_6 | m1_subset_1(k2_partfun1(A_5, B_6, D_8, C_7), k1_zfmisc_1(k2_zfmisc_1(C_7, B_6))) | ~r1_tarski(C_7, A_5) | ~m1_subset_1(D_8, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(D_8, A_5, B_6) | ~v1_funct_1(D_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.82/2.61  tff(c_761, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_747, c_10])).
% 7.82/2.61  tff(c_781, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_761])).
% 7.82/2.61  tff(c_782, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_419, c_781])).
% 7.82/2.61  tff(c_1102, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_995, c_782])).
% 7.82/2.61  tff(c_30, plain, (![C_56, E_62, A_32, D_60, B_48]: (k3_tmap_1(A_32, B_48, C_56, D_60, E_62)=k2_partfun1(u1_struct_0(C_56), u1_struct_0(B_48), E_62, u1_struct_0(D_60)) | ~m1_pre_topc(D_60, C_56) | ~m1_subset_1(E_62, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_56), u1_struct_0(B_48)))) | ~v1_funct_2(E_62, u1_struct_0(C_56), u1_struct_0(B_48)) | ~v1_funct_1(E_62) | ~m1_pre_topc(D_60, A_32) | ~m1_pre_topc(C_56, A_32) | ~l1_pre_topc(B_48) | ~v2_pre_topc(B_48) | v2_struct_0(B_48) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.82/2.61  tff(c_1106, plain, (![A_32, D_60]: (k3_tmap_1(A_32, '#skF_2', '#skF_4', D_60, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_60)) | ~m1_pre_topc(D_60, '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')) | ~m1_pre_topc(D_60, A_32) | ~m1_pre_topc('#skF_4', A_32) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(resolution, [status(thm)], [c_1102, c_30])).
% 7.82/2.61  tff(c_1121, plain, (![A_32, D_60]: (k3_tmap_1(A_32, '#skF_2', '#skF_4', D_60, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_60)) | ~m1_pre_topc(D_60, '#skF_4') | ~m1_pre_topc(D_60, A_32) | ~m1_pre_topc('#skF_4', A_32) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_746, c_994, c_1106])).
% 7.82/2.61  tff(c_2272, plain, (![A_360, D_361]: (k3_tmap_1(A_360, '#skF_2', '#skF_4', D_361, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_361)) | ~m1_pre_topc(D_361, '#skF_4') | ~m1_pre_topc(D_361, A_360) | ~m1_pre_topc('#skF_4', A_360) | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360) | v2_struct_0(A_360))), inference(negUnitSimplification, [status(thm)], [c_66, c_1121])).
% 7.82/2.61  tff(c_118, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_106])).
% 7.82/2.61  tff(c_133, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_118])).
% 7.82/2.61  tff(c_86, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_74])).
% 7.82/2.61  tff(c_97, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_86])).
% 7.82/2.61  tff(c_28, plain, (![A_17, B_25, C_29, D_31]: (k2_partfun1(u1_struct_0(A_17), u1_struct_0(B_25), C_29, u1_struct_0(D_31))=k2_tmap_1(A_17, B_25, C_29, D_31) | ~m1_pre_topc(D_31, A_17) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_17), u1_struct_0(B_25)))) | ~v1_funct_2(C_29, u1_struct_0(A_17), u1_struct_0(B_25)) | ~v1_funct_1(C_29) | ~l1_pre_topc(B_25) | ~v2_pre_topc(B_25) | v2_struct_0(B_25) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.82/2.61  tff(c_1108, plain, (![D_31]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_31))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_31) | ~m1_pre_topc(D_31, '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1102, c_28])).
% 7.82/2.61  tff(c_1125, plain, (![D_31]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_31))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_31) | ~m1_pre_topc(D_31, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_97, c_64, c_62, c_746, c_994, c_1108])).
% 7.82/2.61  tff(c_1126, plain, (![D_31]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_31))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_31) | ~m1_pre_topc(D_31, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_66, c_1125])).
% 7.82/2.61  tff(c_3036, plain, (![A_412, D_413]: (k3_tmap_1(A_412, '#skF_2', '#skF_4', D_413, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_413) | ~m1_pre_topc(D_413, '#skF_4') | ~m1_pre_topc(D_413, '#skF_4') | ~m1_pre_topc(D_413, A_412) | ~m1_pre_topc('#skF_4', A_412) | ~l1_pre_topc(A_412) | ~v2_pre_topc(A_412) | v2_struct_0(A_412))), inference(superposition, [status(thm), theory('equality')], [c_2272, c_1126])).
% 7.82/2.61  tff(c_34, plain, (![A_66, B_82, E_96, D_94, C_90]: (r2_funct_2(u1_struct_0(C_90), u1_struct_0(B_82), k3_tmap_1(A_66, B_82, D_94, C_90, k2_tmap_1(A_66, B_82, E_96, D_94)), k2_tmap_1(A_66, B_82, E_96, C_90)) | ~m1_pre_topc(C_90, D_94) | ~m1_subset_1(E_96, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_66), u1_struct_0(B_82)))) | ~v1_funct_2(E_96, u1_struct_0(A_66), u1_struct_0(B_82)) | ~v1_funct_1(E_96) | ~m1_pre_topc(D_94, A_66) | v2_struct_0(D_94) | ~m1_pre_topc(C_90, A_66) | v2_struct_0(C_90) | ~l1_pre_topc(B_82) | ~v2_pre_topc(B_82) | v2_struct_0(B_82) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_185])).
% 7.82/2.61  tff(c_3064, plain, (![D_413]: (r2_funct_2(u1_struct_0(D_413), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_413), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_413)) | ~m1_pre_topc(D_413, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~m1_pre_topc(D_413, '#skF_3') | v2_struct_0(D_413) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(D_413, '#skF_4') | ~m1_pre_topc(D_413, '#skF_4') | ~m1_pre_topc(D_413, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3036, c_34])).
% 7.82/2.61  tff(c_3076, plain, (![D_413]: (r2_funct_2(u1_struct_0(D_413), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_413), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_413)) | v2_struct_0('#skF_4') | v2_struct_0(D_413) | v2_struct_0('#skF_2') | ~m1_pre_topc(D_413, '#skF_4') | ~m1_pre_topc(D_413, '#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_100, c_48, c_136, c_100, c_64, c_62, c_48, c_44, c_42, c_40, c_3064])).
% 7.82/2.61  tff(c_3079, plain, (![D_414]: (r2_funct_2(u1_struct_0(D_414), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_414), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_414)) | v2_struct_0(D_414) | ~m1_pre_topc(D_414, '#skF_4') | ~m1_pre_topc(D_414, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_66, c_56, c_3076])).
% 7.82/2.61  tff(c_674, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_619])).
% 7.82/2.61  tff(c_869, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_674, c_466])).
% 7.82/2.61  tff(c_889, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_675, c_869])).
% 7.82/2.61  tff(c_38, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.82/2.61  tff(c_748, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_651, c_38])).
% 7.82/2.61  tff(c_1205, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_889, c_748])).
% 7.82/2.61  tff(c_3060, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), '#skF_5'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3036, c_1205])).
% 7.82/2.61  tff(c_3073, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), '#skF_5'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_50, c_46, c_46, c_3060])).
% 7.82/2.61  tff(c_3074, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), '#skF_5'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_3073])).
% 7.82/2.61  tff(c_3082, plain, (v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_3079, c_3074])).
% 7.82/2.61  tff(c_3085, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_675, c_46, c_3082])).
% 7.82/2.61  tff(c_3087, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_3085])).
% 7.82/2.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.82/2.61  
% 7.82/2.61  Inference rules
% 7.82/2.61  ----------------------
% 7.82/2.61  #Ref     : 0
% 7.82/2.61  #Sup     : 630
% 7.82/2.61  #Fact    : 0
% 7.82/2.61  #Define  : 0
% 7.82/2.61  #Split   : 14
% 7.82/2.61  #Chain   : 0
% 7.82/2.61  #Close   : 0
% 7.82/2.61  
% 7.82/2.61  Ordering : KBO
% 7.82/2.61  
% 7.82/2.61  Simplification rules
% 7.82/2.61  ----------------------
% 7.82/2.61  #Subsume      : 130
% 7.82/2.61  #Demod        : 1193
% 7.82/2.61  #Tautology    : 106
% 7.82/2.61  #SimpNegUnit  : 191
% 7.82/2.61  #BackRed      : 10
% 7.82/2.61  
% 7.82/2.61  #Partial instantiations: 0
% 7.82/2.61  #Strategies tried      : 1
% 7.82/2.61  
% 7.82/2.61  Timing (in seconds)
% 7.82/2.61  ----------------------
% 7.82/2.61  Preprocessing        : 0.36
% 7.82/2.61  Parsing              : 0.19
% 7.82/2.61  CNF conversion       : 0.04
% 7.82/2.61  Main loop            : 1.40
% 7.82/2.61  Inferencing          : 0.45
% 7.82/2.61  Reduction            : 0.51
% 7.82/2.61  Demodulation         : 0.39
% 7.82/2.61  BG Simplification    : 0.06
% 7.82/2.61  Subsumption          : 0.32
% 7.82/2.62  Abstraction          : 0.07
% 7.82/2.62  MUC search           : 0.00
% 7.82/2.62  Cooper               : 0.00
% 7.82/2.62  Total                : 1.81
% 7.82/2.62  Index Insertion      : 0.00
% 7.82/2.62  Index Deletion       : 0.00
% 7.82/2.62  Index Matching       : 0.00
% 7.82/2.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
