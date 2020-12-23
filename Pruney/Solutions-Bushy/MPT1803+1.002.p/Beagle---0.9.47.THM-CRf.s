%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1803+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:26 EST 2020

% Result     : Theorem 47.47s
% Output     : CNFRefutation 47.74s
% Verified   : 
% Statistics : Number of formulae       :  234 (31732 expanded)
%              Number of leaves         :   50 (10909 expanded)
%              Depth                    :   49
%              Number of atoms          : 1266 (211041 expanded)
%              Number of equality atoms :  118 (17883 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r1_tmap_1 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k9_tmap_1 > k8_tmap_1 > k7_tmap_1 > k7_relat_1 > k6_tmap_1 > k5_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k9_tmap_1,type,(
    k9_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_314,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => r1_tmap_1(B,k8_tmap_1(A,B),k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),B),C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_tmap_1)).

tff(f_278,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_167,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_148,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( ( v1_pre_topc(C)
                & v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( C = k8_tmap_1(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( D = u1_struct_0(B)
                     => C = k6_tmap_1(A,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B))))) )
             => ( C = k9_tmap_1(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( D = u1_struct_0(B)
                     => r1_funct_2(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,D)),C,k7_tmap_1(A,D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_tmap_1)).

tff(f_174,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_284,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_290,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_182,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_271,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ( u1_struct_0(k8_tmap_1(A,B)) = u1_struct_0(A)
            & ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => u1_pre_topc(k8_tmap_1(A,B)) = k5_tmap_1(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).

tff(f_163,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k9_tmap_1(A,B))
        & v1_funct_2(k9_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)))
        & m1_subset_1(k9_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_tmap_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_198,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_249,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( u1_struct_0(C) = B
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(C))
                   => r1_tmap_1(C,k6_tmap_1(A,B),k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_tmap_1)).

tff(f_226,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(c_84,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_80,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_68,plain,(
    ! [B_109,A_107] :
      ( m1_subset_1(u1_struct_0(B_109),k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ m1_pre_topc(B_109,A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_44,plain,(
    ! [A_68] :
      ( l1_struct_0(A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_124,plain,(
    ! [A_149,B_150] :
      ( v1_funct_1(k7_tmap_1(A_149,B_150))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149)
      | ~ v2_pre_topc(A_149)
      | v2_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_128,plain,(
    ! [A_107,B_109] :
      ( v1_funct_1(k7_tmap_1(A_107,u1_struct_0(B_109)))
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107)
      | ~ m1_pre_topc(B_109,A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_68,c_124])).

tff(c_32,plain,(
    ! [A_64,B_65] :
      ( l1_pre_topc(k8_tmap_1(A_64,B_65))
      | ~ m1_pre_topc(B_65,A_64)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_36,plain,(
    ! [A_64,B_65] :
      ( v1_pre_topc(k8_tmap_1(A_64,B_65))
      | ~ m1_pre_topc(B_65,A_64)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_34,plain,(
    ! [A_64,B_65] :
      ( v2_pre_topc(k8_tmap_1(A_64,B_65))
      | ~ m1_pre_topc(B_65,A_64)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_354,plain,(
    ! [A_228,B_229] :
      ( k6_tmap_1(A_228,u1_struct_0(B_229)) = k8_tmap_1(A_228,B_229)
      | ~ m1_subset_1(u1_struct_0(B_229),k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ l1_pre_topc(k8_tmap_1(A_228,B_229))
      | ~ v2_pre_topc(k8_tmap_1(A_228,B_229))
      | ~ v1_pre_topc(k8_tmap_1(A_228,B_229))
      | ~ m1_pre_topc(B_229,A_228)
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_392,plain,(
    ! [A_262,B_263] :
      ( k6_tmap_1(A_262,u1_struct_0(B_263)) = k8_tmap_1(A_262,B_263)
      | ~ l1_pre_topc(k8_tmap_1(A_262,B_263))
      | ~ v2_pre_topc(k8_tmap_1(A_262,B_263))
      | ~ v1_pre_topc(k8_tmap_1(A_262,B_263))
      | ~ v2_pre_topc(A_262)
      | v2_struct_0(A_262)
      | ~ m1_pre_topc(B_263,A_262)
      | ~ l1_pre_topc(A_262) ) ),
    inference(resolution,[status(thm)],[c_68,c_354])).

tff(c_397,plain,(
    ! [A_264,B_265] :
      ( k6_tmap_1(A_264,u1_struct_0(B_265)) = k8_tmap_1(A_264,B_265)
      | ~ l1_pre_topc(k8_tmap_1(A_264,B_265))
      | ~ v1_pre_topc(k8_tmap_1(A_264,B_265))
      | ~ m1_pre_topc(B_265,A_264)
      | ~ l1_pre_topc(A_264)
      | ~ v2_pre_topc(A_264)
      | v2_struct_0(A_264) ) ),
    inference(resolution,[status(thm)],[c_34,c_392])).

tff(c_402,plain,(
    ! [A_266,B_267] :
      ( k6_tmap_1(A_266,u1_struct_0(B_267)) = k8_tmap_1(A_266,B_267)
      | ~ l1_pre_topc(k8_tmap_1(A_266,B_267))
      | ~ m1_pre_topc(B_267,A_266)
      | ~ l1_pre_topc(A_266)
      | ~ v2_pre_topc(A_266)
      | v2_struct_0(A_266) ) ),
    inference(resolution,[status(thm)],[c_36,c_397])).

tff(c_407,plain,(
    ! [A_268,B_269] :
      ( k6_tmap_1(A_268,u1_struct_0(B_269)) = k8_tmap_1(A_268,B_269)
      | ~ m1_pre_topc(B_269,A_268)
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268) ) ),
    inference(resolution,[status(thm)],[c_32,c_402])).

tff(c_28,plain,(
    ! [A_62,B_63] :
      ( v1_funct_2(k7_tmap_1(A_62,B_63),u1_struct_0(A_62),u1_struct_0(k6_tmap_1(A_62,B_63)))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_427,plain,(
    ! [A_268,B_269] :
      ( v1_funct_2(k7_tmap_1(A_268,u1_struct_0(B_269)),u1_struct_0(A_268),u1_struct_0(k8_tmap_1(A_268,B_269)))
      | ~ m1_subset_1(u1_struct_0(B_269),k1_zfmisc_1(u1_struct_0(A_268)))
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268)
      | ~ m1_pre_topc(B_269,A_268)
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_28])).

tff(c_26,plain,(
    ! [A_62,B_63] :
      ( m1_subset_1(k7_tmap_1(A_62,B_63),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_62),u1_struct_0(k6_tmap_1(A_62,B_63)))))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_683,plain,(
    ! [A_350,B_351] :
      ( m1_subset_1(k7_tmap_1(A_350,u1_struct_0(B_351)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_350),u1_struct_0(k8_tmap_1(A_350,B_351)))))
      | ~ m1_subset_1(u1_struct_0(B_351),k1_zfmisc_1(u1_struct_0(A_350)))
      | ~ l1_pre_topc(A_350)
      | ~ v2_pre_topc(A_350)
      | v2_struct_0(A_350)
      | ~ m1_pre_topc(B_351,A_350)
      | ~ l1_pre_topc(A_350)
      | ~ v2_pre_topc(A_350)
      | v2_struct_0(A_350) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_26])).

tff(c_14,plain,(
    ! [B_35,A_23,C_41] :
      ( u1_struct_0(B_35) = '#skF_2'(A_23,B_35,C_41)
      | k9_tmap_1(A_23,B_35) = C_41
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_23),u1_struct_0(k8_tmap_1(A_23,B_35)))))
      | ~ v1_funct_2(C_41,u1_struct_0(A_23),u1_struct_0(k8_tmap_1(A_23,B_35)))
      | ~ v1_funct_1(C_41)
      | ~ m1_pre_topc(B_35,A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1392,plain,(
    ! [A_483,B_484] :
      ( '#skF_2'(A_483,B_484,k7_tmap_1(A_483,u1_struct_0(B_484))) = u1_struct_0(B_484)
      | k7_tmap_1(A_483,u1_struct_0(B_484)) = k9_tmap_1(A_483,B_484)
      | ~ v1_funct_2(k7_tmap_1(A_483,u1_struct_0(B_484)),u1_struct_0(A_483),u1_struct_0(k8_tmap_1(A_483,B_484)))
      | ~ v1_funct_1(k7_tmap_1(A_483,u1_struct_0(B_484)))
      | ~ m1_subset_1(u1_struct_0(B_484),k1_zfmisc_1(u1_struct_0(A_483)))
      | ~ m1_pre_topc(B_484,A_483)
      | ~ l1_pre_topc(A_483)
      | ~ v2_pre_topc(A_483)
      | v2_struct_0(A_483) ) ),
    inference(resolution,[status(thm)],[c_683,c_14])).

tff(c_1409,plain,(
    ! [A_485,B_486] :
      ( '#skF_2'(A_485,B_486,k7_tmap_1(A_485,u1_struct_0(B_486))) = u1_struct_0(B_486)
      | k7_tmap_1(A_485,u1_struct_0(B_486)) = k9_tmap_1(A_485,B_486)
      | ~ v1_funct_1(k7_tmap_1(A_485,u1_struct_0(B_486)))
      | ~ m1_subset_1(u1_struct_0(B_486),k1_zfmisc_1(u1_struct_0(A_485)))
      | ~ m1_pre_topc(B_486,A_485)
      | ~ l1_pre_topc(A_485)
      | ~ v2_pre_topc(A_485)
      | v2_struct_0(A_485) ) ),
    inference(resolution,[status(thm)],[c_427,c_1392])).

tff(c_1417,plain,(
    ! [A_487,B_488] :
      ( '#skF_2'(A_487,B_488,k7_tmap_1(A_487,u1_struct_0(B_488))) = u1_struct_0(B_488)
      | k7_tmap_1(A_487,u1_struct_0(B_488)) = k9_tmap_1(A_487,B_488)
      | ~ v1_funct_1(k7_tmap_1(A_487,u1_struct_0(B_488)))
      | ~ v2_pre_topc(A_487)
      | v2_struct_0(A_487)
      | ~ m1_pre_topc(B_488,A_487)
      | ~ l1_pre_topc(A_487) ) ),
    inference(resolution,[status(thm)],[c_68,c_1409])).

tff(c_1425,plain,(
    ! [A_107,B_109] :
      ( '#skF_2'(A_107,B_109,k7_tmap_1(A_107,u1_struct_0(B_109))) = u1_struct_0(B_109)
      | k7_tmap_1(A_107,u1_struct_0(B_109)) = k9_tmap_1(A_107,B_109)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107)
      | ~ m1_pre_topc(B_109,A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_128,c_1417])).

tff(c_78,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_91,plain,(
    ! [B_124,A_125] :
      ( l1_pre_topc(B_124)
      | ~ m1_pre_topc(B_124,A_125)
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_94,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_91])).

tff(c_97,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_94])).

tff(c_70,plain,(
    ! [A_110,B_111] :
      ( r2_hidden(A_110,B_111)
      | v1_xboole_0(B_111)
      | ~ m1_subset_1(A_110,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_284])).

tff(c_105,plain,(
    ! [B_132,A_133] :
      ( m1_subset_1(u1_struct_0(B_132),k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ m1_pre_topc(B_132,A_133)
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_72,plain,(
    ! [A_112,C_114,B_113] :
      ( m1_subset_1(A_112,C_114)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(C_114))
      | ~ r2_hidden(A_112,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_118,plain,(
    ! [A_144,A_145,B_146] :
      ( m1_subset_1(A_144,u1_struct_0(A_145))
      | ~ r2_hidden(A_144,u1_struct_0(B_146))
      | ~ m1_pre_topc(B_146,A_145)
      | ~ l1_pre_topc(A_145) ) ),
    inference(resolution,[status(thm)],[c_105,c_72])).

tff(c_149,plain,(
    ! [A_169,A_170,B_171] :
      ( m1_subset_1(A_169,u1_struct_0(A_170))
      | ~ m1_pre_topc(B_171,A_170)
      | ~ l1_pre_topc(A_170)
      | v1_xboole_0(u1_struct_0(B_171))
      | ~ m1_subset_1(A_169,u1_struct_0(B_171)) ) ),
    inference(resolution,[status(thm)],[c_70,c_118])).

tff(c_151,plain,(
    ! [A_169] :
      ( m1_subset_1(A_169,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_169,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_80,c_149])).

tff(c_154,plain,(
    ! [A_169] :
      ( m1_subset_1(A_169,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_169,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_151])).

tff(c_155,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_48,plain,(
    ! [A_72] :
      ( ~ v1_xboole_0(u1_struct_0(A_72))
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_158,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_155,c_48])).

tff(c_161,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_158])).

tff(c_164,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_161])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_164])).

tff(c_169,plain,(
    ! [A_169] :
      ( m1_subset_1(A_169,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_169,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_16,plain,(
    ! [A_23,B_35,C_41] :
      ( m1_subset_1('#skF_2'(A_23,B_35,C_41),k1_zfmisc_1(u1_struct_0(A_23)))
      | k9_tmap_1(A_23,B_35) = C_41
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_23),u1_struct_0(k8_tmap_1(A_23,B_35)))))
      | ~ v1_funct_2(C_41,u1_struct_0(A_23),u1_struct_0(k8_tmap_1(A_23,B_35)))
      | ~ v1_funct_1(C_41)
      | ~ m1_pre_topc(B_35,A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2092,plain,(
    ! [A_547,B_548] :
      ( m1_subset_1('#skF_2'(A_547,B_548,k7_tmap_1(A_547,u1_struct_0(B_548))),k1_zfmisc_1(u1_struct_0(A_547)))
      | k7_tmap_1(A_547,u1_struct_0(B_548)) = k9_tmap_1(A_547,B_548)
      | ~ v1_funct_2(k7_tmap_1(A_547,u1_struct_0(B_548)),u1_struct_0(A_547),u1_struct_0(k8_tmap_1(A_547,B_548)))
      | ~ v1_funct_1(k7_tmap_1(A_547,u1_struct_0(B_548)))
      | ~ m1_subset_1(u1_struct_0(B_548),k1_zfmisc_1(u1_struct_0(A_547)))
      | ~ m1_pre_topc(B_548,A_547)
      | ~ l1_pre_topc(A_547)
      | ~ v2_pre_topc(A_547)
      | v2_struct_0(A_547) ) ),
    inference(resolution,[status(thm)],[c_683,c_16])).

tff(c_2112,plain,(
    ! [A_549,B_550] :
      ( m1_subset_1('#skF_2'(A_549,B_550,k7_tmap_1(A_549,u1_struct_0(B_550))),k1_zfmisc_1(u1_struct_0(A_549)))
      | k7_tmap_1(A_549,u1_struct_0(B_550)) = k9_tmap_1(A_549,B_550)
      | ~ v1_funct_1(k7_tmap_1(A_549,u1_struct_0(B_550)))
      | ~ m1_subset_1(u1_struct_0(B_550),k1_zfmisc_1(u1_struct_0(A_549)))
      | ~ m1_pre_topc(B_550,A_549)
      | ~ l1_pre_topc(A_549)
      | ~ v2_pre_topc(A_549)
      | v2_struct_0(A_549) ) ),
    inference(resolution,[status(thm)],[c_427,c_2092])).

tff(c_2195,plain,(
    ! [A_561,A_562,B_563] :
      ( m1_subset_1(A_561,u1_struct_0(A_562))
      | ~ r2_hidden(A_561,'#skF_2'(A_562,B_563,k7_tmap_1(A_562,u1_struct_0(B_563))))
      | k7_tmap_1(A_562,u1_struct_0(B_563)) = k9_tmap_1(A_562,B_563)
      | ~ v1_funct_1(k7_tmap_1(A_562,u1_struct_0(B_563)))
      | ~ m1_subset_1(u1_struct_0(B_563),k1_zfmisc_1(u1_struct_0(A_562)))
      | ~ m1_pre_topc(B_563,A_562)
      | ~ l1_pre_topc(A_562)
      | ~ v2_pre_topc(A_562)
      | v2_struct_0(A_562) ) ),
    inference(resolution,[status(thm)],[c_2112,c_72])).

tff(c_2207,plain,(
    ! [A_564,A_565,B_566] :
      ( m1_subset_1(A_564,u1_struct_0(A_565))
      | k7_tmap_1(A_565,u1_struct_0(B_566)) = k9_tmap_1(A_565,B_566)
      | ~ v1_funct_1(k7_tmap_1(A_565,u1_struct_0(B_566)))
      | ~ m1_subset_1(u1_struct_0(B_566),k1_zfmisc_1(u1_struct_0(A_565)))
      | ~ m1_pre_topc(B_566,A_565)
      | ~ l1_pre_topc(A_565)
      | ~ v2_pre_topc(A_565)
      | v2_struct_0(A_565)
      | v1_xboole_0('#skF_2'(A_565,B_566,k7_tmap_1(A_565,u1_struct_0(B_566))))
      | ~ m1_subset_1(A_564,'#skF_2'(A_565,B_566,k7_tmap_1(A_565,u1_struct_0(B_566)))) ) ),
    inference(resolution,[status(thm)],[c_70,c_2195])).

tff(c_2215,plain,(
    ! [A_567,A_568,B_569] :
      ( m1_subset_1(A_567,u1_struct_0(A_568))
      | k7_tmap_1(A_568,u1_struct_0(B_569)) = k9_tmap_1(A_568,B_569)
      | ~ v1_funct_1(k7_tmap_1(A_568,u1_struct_0(B_569)))
      | ~ v2_pre_topc(A_568)
      | v2_struct_0(A_568)
      | v1_xboole_0('#skF_2'(A_568,B_569,k7_tmap_1(A_568,u1_struct_0(B_569))))
      | ~ m1_subset_1(A_567,'#skF_2'(A_568,B_569,k7_tmap_1(A_568,u1_struct_0(B_569))))
      | ~ m1_pre_topc(B_569,A_568)
      | ~ l1_pre_topc(A_568) ) ),
    inference(resolution,[status(thm)],[c_68,c_2207])).

tff(c_3357,plain,(
    ! [A_613,A_614,B_615] :
      ( m1_subset_1(A_613,u1_struct_0(A_614))
      | k7_tmap_1(A_614,u1_struct_0(B_615)) = k9_tmap_1(A_614,B_615)
      | ~ v1_funct_1(k7_tmap_1(A_614,u1_struct_0(B_615)))
      | ~ v2_pre_topc(A_614)
      | v2_struct_0(A_614)
      | v1_xboole_0('#skF_2'(A_614,B_615,k7_tmap_1(A_614,u1_struct_0(B_615))))
      | ~ m1_subset_1(A_613,u1_struct_0(B_615))
      | ~ m1_pre_topc(B_615,A_614)
      | ~ l1_pre_topc(A_614)
      | k7_tmap_1(A_614,u1_struct_0(B_615)) = k9_tmap_1(A_614,B_615)
      | ~ v2_pre_topc(A_614)
      | v2_struct_0(A_614)
      | ~ m1_pre_topc(B_615,A_614)
      | ~ l1_pre_topc(A_614) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1425,c_2215])).

tff(c_3422,plain,(
    ! [A_620,A_621] :
      ( m1_subset_1(A_620,u1_struct_0(A_621))
      | ~ v1_funct_1(k7_tmap_1(A_621,u1_struct_0('#skF_3')))
      | v1_xboole_0('#skF_2'(A_621,'#skF_3',k7_tmap_1(A_621,u1_struct_0('#skF_3'))))
      | k7_tmap_1(A_621,u1_struct_0('#skF_3')) = k9_tmap_1(A_621,'#skF_3')
      | ~ v2_pre_topc(A_621)
      | v2_struct_0(A_621)
      | ~ m1_pre_topc('#skF_3',A_621)
      | ~ l1_pre_topc(A_621)
      | ~ m1_subset_1(A_620,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_169,c_3357])).

tff(c_3426,plain,(
    ! [A_622] :
      ( m1_subset_1('#skF_5',u1_struct_0(A_622))
      | ~ v1_funct_1(k7_tmap_1(A_622,u1_struct_0('#skF_3')))
      | v1_xboole_0('#skF_2'(A_622,'#skF_3',k7_tmap_1(A_622,u1_struct_0('#skF_3'))))
      | k7_tmap_1(A_622,u1_struct_0('#skF_3')) = k9_tmap_1(A_622,'#skF_3')
      | ~ v2_pre_topc(A_622)
      | v2_struct_0(A_622)
      | ~ m1_pre_topc('#skF_3',A_622)
      | ~ l1_pre_topc(A_622) ) ),
    inference(resolution,[status(thm)],[c_78,c_3422])).

tff(c_3430,plain,(
    ! [A_107] :
      ( m1_subset_1('#skF_5',u1_struct_0(A_107))
      | ~ v1_funct_1(k7_tmap_1(A_107,u1_struct_0('#skF_3')))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | k7_tmap_1(A_107,u1_struct_0('#skF_3')) = k9_tmap_1(A_107,'#skF_3')
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107)
      | ~ m1_pre_topc('#skF_3',A_107)
      | ~ l1_pre_topc(A_107)
      | k7_tmap_1(A_107,u1_struct_0('#skF_3')) = k9_tmap_1(A_107,'#skF_3')
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107)
      | ~ m1_pre_topc('#skF_3',A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1425,c_3426])).

tff(c_3431,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3430])).

tff(c_3436,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3431,c_48])).

tff(c_3443,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3436])).

tff(c_3446,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_3443])).

tff(c_3450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3446])).

tff(c_3452,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3430])).

tff(c_86,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_66,plain,(
    ! [A_100,B_104] :
      ( u1_struct_0(k8_tmap_1(A_100,B_104)) = u1_struct_0(A_100)
      | ~ m1_pre_topc(B_104,A_100)
      | v2_struct_0(B_104)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_40,plain,(
    ! [A_66,B_67] :
      ( v1_funct_2(k9_tmap_1(A_66,B_67),u1_struct_0(A_66),u1_struct_0(k8_tmap_1(A_66,B_67)))
      | ~ m1_pre_topc(B_67,A_66)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_38,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1(k9_tmap_1(A_66,B_67),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_66),u1_struct_0(k8_tmap_1(A_66,B_67)))))
      | ~ m1_pre_topc(B_67,A_66)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_42,plain,(
    ! [A_66,B_67] :
      ( v1_funct_1(k9_tmap_1(A_66,B_67))
      | ~ m1_pre_topc(B_67,A_66)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_406,plain,(
    ! [A_64,B_65] :
      ( k6_tmap_1(A_64,u1_struct_0(B_65)) = k8_tmap_1(A_64,B_65)
      | ~ m1_pre_topc(B_65,A_64)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_32,c_402])).

tff(c_135,plain,(
    ! [A_155,B_156] :
      ( l1_pre_topc(k6_tmap_1(A_155,B_156))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_139,plain,(
    ! [A_107,B_109] :
      ( l1_pre_topc(k6_tmap_1(A_107,u1_struct_0(B_109)))
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107)
      | ~ m1_pre_topc(B_109,A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_68,c_135])).

tff(c_130,plain,(
    ! [A_153,B_154] :
      ( v1_pre_topc(k6_tmap_1(A_153,B_154))
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_134,plain,(
    ! [A_107,B_109] :
      ( v1_pre_topc(k6_tmap_1(A_107,u1_struct_0(B_109)))
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107)
      | ~ m1_pre_topc(B_109,A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_68,c_130])).

tff(c_142,plain,(
    ! [A_161,B_162] :
      ( v2_pre_topc(k6_tmap_1(A_161,B_162))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161)
      | v2_struct_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_146,plain,(
    ! [A_107,B_109] :
      ( v2_pre_topc(k6_tmap_1(A_107,u1_struct_0(B_109)))
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107)
      | ~ m1_pre_topc(B_109,A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_68,c_142])).

tff(c_265,plain,(
    ! [B_191,A_192,C_193] :
      ( u1_struct_0(B_191) = '#skF_1'(A_192,B_191,C_193)
      | k8_tmap_1(A_192,B_191) = C_193
      | ~ l1_pre_topc(C_193)
      | ~ v2_pre_topc(C_193)
      | ~ v1_pre_topc(C_193)
      | ~ m1_pre_topc(B_191,A_192)
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_932,plain,(
    ! [A_413,B_414,A_415,B_416] :
      ( '#skF_1'(A_413,B_414,k6_tmap_1(A_415,u1_struct_0(B_416))) = u1_struct_0(B_414)
      | k8_tmap_1(A_413,B_414) = k6_tmap_1(A_415,u1_struct_0(B_416))
      | ~ l1_pre_topc(k6_tmap_1(A_415,u1_struct_0(B_416)))
      | ~ v1_pre_topc(k6_tmap_1(A_415,u1_struct_0(B_416)))
      | ~ m1_pre_topc(B_414,A_413)
      | ~ l1_pre_topc(A_413)
      | ~ v2_pre_topc(A_413)
      | v2_struct_0(A_413)
      | ~ v2_pre_topc(A_415)
      | v2_struct_0(A_415)
      | ~ m1_pre_topc(B_416,A_415)
      | ~ l1_pre_topc(A_415) ) ),
    inference(resolution,[status(thm)],[c_146,c_265])).

tff(c_943,plain,(
    ! [A_417,B_418,A_419,B_420] :
      ( '#skF_1'(A_417,B_418,k6_tmap_1(A_419,u1_struct_0(B_420))) = u1_struct_0(B_418)
      | k8_tmap_1(A_417,B_418) = k6_tmap_1(A_419,u1_struct_0(B_420))
      | ~ l1_pre_topc(k6_tmap_1(A_419,u1_struct_0(B_420)))
      | ~ m1_pre_topc(B_418,A_417)
      | ~ l1_pre_topc(A_417)
      | ~ v2_pre_topc(A_417)
      | v2_struct_0(A_417)
      | ~ v2_pre_topc(A_419)
      | v2_struct_0(A_419)
      | ~ m1_pre_topc(B_420,A_419)
      | ~ l1_pre_topc(A_419) ) ),
    inference(resolution,[status(thm)],[c_134,c_932])).

tff(c_954,plain,(
    ! [A_421,B_422,A_423,B_424] :
      ( '#skF_1'(A_421,B_422,k6_tmap_1(A_423,u1_struct_0(B_424))) = u1_struct_0(B_422)
      | k8_tmap_1(A_421,B_422) = k6_tmap_1(A_423,u1_struct_0(B_424))
      | ~ m1_pre_topc(B_422,A_421)
      | ~ l1_pre_topc(A_421)
      | ~ v2_pre_topc(A_421)
      | v2_struct_0(A_421)
      | ~ v2_pre_topc(A_423)
      | v2_struct_0(A_423)
      | ~ m1_pre_topc(B_424,A_423)
      | ~ l1_pre_topc(A_423) ) ),
    inference(resolution,[status(thm)],[c_139,c_943])).

tff(c_1002,plain,(
    ! [A_429,B_430,A_431,B_432] :
      ( '#skF_1'(A_429,B_430,k8_tmap_1(A_431,B_432)) = u1_struct_0(B_430)
      | k8_tmap_1(A_429,B_430) = k6_tmap_1(A_431,u1_struct_0(B_432))
      | ~ m1_pre_topc(B_430,A_429)
      | ~ l1_pre_topc(A_429)
      | ~ v2_pre_topc(A_429)
      | v2_struct_0(A_429)
      | ~ v2_pre_topc(A_431)
      | v2_struct_0(A_431)
      | ~ m1_pre_topc(B_432,A_431)
      | ~ l1_pre_topc(A_431)
      | ~ m1_pre_topc(B_432,A_431)
      | ~ l1_pre_topc(A_431)
      | ~ v2_pre_topc(A_431)
      | v2_struct_0(A_431) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_954])).

tff(c_2383,plain,(
    ! [A_600,B_601,A_602,B_603] :
      ( u1_struct_0(k6_tmap_1(A_600,u1_struct_0(B_601))) = u1_struct_0(A_602)
      | ~ m1_pre_topc(B_603,A_602)
      | v2_struct_0(B_603)
      | ~ l1_pre_topc(A_602)
      | ~ v2_pre_topc(A_602)
      | v2_struct_0(A_602)
      | '#skF_1'(A_602,B_603,k8_tmap_1(A_600,B_601)) = u1_struct_0(B_603)
      | ~ m1_pre_topc(B_603,A_602)
      | ~ l1_pre_topc(A_602)
      | ~ v2_pre_topc(A_602)
      | v2_struct_0(A_602)
      | ~ v2_pre_topc(A_600)
      | v2_struct_0(A_600)
      | ~ m1_pre_topc(B_601,A_600)
      | ~ l1_pre_topc(A_600)
      | ~ m1_pre_topc(B_601,A_600)
      | ~ l1_pre_topc(A_600)
      | ~ v2_pre_topc(A_600)
      | v2_struct_0(A_600) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1002,c_66])).

tff(c_11148,plain,(
    ! [B_1030,B_1033,A_1031,A_1029,B_1032] :
      ( m1_subset_1(u1_struct_0(B_1033),k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_1031,u1_struct_0(B_1032)))))
      | ~ m1_pre_topc(B_1033,A_1029)
      | ~ l1_pre_topc(A_1029)
      | ~ m1_pre_topc(B_1030,A_1029)
      | v2_struct_0(B_1030)
      | ~ l1_pre_topc(A_1029)
      | ~ v2_pre_topc(A_1029)
      | v2_struct_0(A_1029)
      | '#skF_1'(A_1029,B_1030,k8_tmap_1(A_1031,B_1032)) = u1_struct_0(B_1030)
      | ~ m1_pre_topc(B_1030,A_1029)
      | ~ l1_pre_topc(A_1029)
      | ~ v2_pre_topc(A_1029)
      | v2_struct_0(A_1029)
      | ~ v2_pre_topc(A_1031)
      | v2_struct_0(A_1031)
      | ~ m1_pre_topc(B_1032,A_1031)
      | ~ l1_pre_topc(A_1031)
      | ~ m1_pre_topc(B_1032,A_1031)
      | ~ l1_pre_topc(A_1031)
      | ~ v2_pre_topc(A_1031)
      | v2_struct_0(A_1031) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2383,c_68])).

tff(c_11150,plain,(
    ! [A_1031,B_1032,B_1030] :
      ( m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_1031,u1_struct_0(B_1032)))))
      | v2_struct_0(B_1030)
      | '#skF_1'('#skF_3',B_1030,k8_tmap_1(A_1031,B_1032)) = u1_struct_0(B_1030)
      | ~ m1_pre_topc(B_1030,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1032,A_1031)
      | ~ l1_pre_topc(A_1031)
      | ~ v2_pre_topc(A_1031)
      | v2_struct_0(A_1031) ) ),
    inference(resolution,[status(thm)],[c_80,c_11148])).

tff(c_11153,plain,(
    ! [A_1031,B_1032,B_1030] :
      ( m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_1031,u1_struct_0(B_1032)))))
      | v2_struct_0(B_1030)
      | '#skF_1'('#skF_3',B_1030,k8_tmap_1(A_1031,B_1032)) = u1_struct_0(B_1030)
      | ~ m1_pre_topc(B_1030,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1032,A_1031)
      | ~ l1_pre_topc(A_1031)
      | ~ v2_pre_topc(A_1031)
      | v2_struct_0(A_1031) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_11150])).

tff(c_11155,plain,(
    ! [A_1034,B_1035,B_1036] :
      ( m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_1034,u1_struct_0(B_1035)))))
      | v2_struct_0(B_1036)
      | '#skF_1'('#skF_3',B_1036,k8_tmap_1(A_1034,B_1035)) = u1_struct_0(B_1036)
      | ~ m1_pre_topc(B_1036,'#skF_3')
      | ~ m1_pre_topc(B_1035,A_1034)
      | ~ l1_pre_topc(A_1034)
      | ~ v2_pre_topc(A_1034)
      | v2_struct_0(A_1034) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_11153])).

tff(c_13491,plain,(
    ! [A_1044,B_1045,B_1046] :
      ( m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_1044,B_1045))))
      | v2_struct_0(B_1046)
      | '#skF_1'('#skF_3',B_1046,k8_tmap_1(A_1044,B_1045)) = u1_struct_0(B_1046)
      | ~ m1_pre_topc(B_1046,'#skF_3')
      | ~ m1_pre_topc(B_1045,A_1044)
      | ~ l1_pre_topc(A_1044)
      | ~ v2_pre_topc(A_1044)
      | v2_struct_0(A_1044)
      | ~ m1_pre_topc(B_1045,A_1044)
      | ~ l1_pre_topc(A_1044)
      | ~ v2_pre_topc(A_1044)
      | v2_struct_0(A_1044) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_11155])).

tff(c_314,plain,(
    ! [A_211,B_212,C_213] :
      ( m1_subset_1('#skF_1'(A_211,B_212,C_213),k1_zfmisc_1(u1_struct_0(A_211)))
      | k8_tmap_1(A_211,B_212) = C_213
      | ~ l1_pre_topc(C_213)
      | ~ v2_pre_topc(C_213)
      | ~ v1_pre_topc(C_213)
      | ~ m1_pre_topc(B_212,A_211)
      | ~ l1_pre_topc(A_211)
      | ~ v2_pre_topc(A_211)
      | v2_struct_0(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_50,plain,(
    ! [A_73,B_74] :
      ( v2_pre_topc(k6_tmap_1(A_73,B_74))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_335,plain,(
    ! [A_211,B_212,C_213] :
      ( v2_pre_topc(k6_tmap_1(A_211,'#skF_1'(A_211,B_212,C_213)))
      | k8_tmap_1(A_211,B_212) = C_213
      | ~ l1_pre_topc(C_213)
      | ~ v2_pre_topc(C_213)
      | ~ v1_pre_topc(C_213)
      | ~ m1_pre_topc(B_212,A_211)
      | ~ l1_pre_topc(A_211)
      | ~ v2_pre_topc(A_211)
      | v2_struct_0(A_211) ) ),
    inference(resolution,[status(thm)],[c_314,c_50])).

tff(c_13577,plain,(
    ! [B_1046,A_1044,B_1045] :
      ( v2_pre_topc(k6_tmap_1('#skF_3',u1_struct_0(B_1046)))
      | k8_tmap_1(A_1044,B_1045) = k8_tmap_1('#skF_3',B_1046)
      | ~ l1_pre_topc(k8_tmap_1(A_1044,B_1045))
      | ~ v2_pre_topc(k8_tmap_1(A_1044,B_1045))
      | ~ v1_pre_topc(k8_tmap_1(A_1044,B_1045))
      | ~ m1_pre_topc(B_1046,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_1044,B_1045))))
      | v2_struct_0(B_1046)
      | ~ m1_pre_topc(B_1046,'#skF_3')
      | ~ m1_pre_topc(B_1045,A_1044)
      | ~ l1_pre_topc(A_1044)
      | ~ v2_pre_topc(A_1044)
      | v2_struct_0(A_1044)
      | ~ m1_pre_topc(B_1045,A_1044)
      | ~ l1_pre_topc(A_1044)
      | ~ v2_pre_topc(A_1044)
      | v2_struct_0(A_1044) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13491,c_335])).

tff(c_13724,plain,(
    ! [B_1046,A_1044,B_1045] :
      ( v2_pre_topc(k6_tmap_1('#skF_3',u1_struct_0(B_1046)))
      | k8_tmap_1(A_1044,B_1045) = k8_tmap_1('#skF_3',B_1046)
      | ~ l1_pre_topc(k8_tmap_1(A_1044,B_1045))
      | ~ v2_pre_topc(k8_tmap_1(A_1044,B_1045))
      | ~ v1_pre_topc(k8_tmap_1(A_1044,B_1045))
      | v2_struct_0('#skF_3')
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_1044,B_1045))))
      | v2_struct_0(B_1046)
      | ~ m1_pre_topc(B_1046,'#skF_3')
      | ~ m1_pre_topc(B_1045,A_1044)
      | ~ l1_pre_topc(A_1044)
      | ~ v2_pre_topc(A_1044)
      | v2_struct_0(A_1044) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_13577])).

tff(c_30644,plain,(
    ! [B_1216,A_1217,B_1218] :
      ( v2_pre_topc(k6_tmap_1('#skF_3',u1_struct_0(B_1216)))
      | k8_tmap_1(A_1217,B_1218) = k8_tmap_1('#skF_3',B_1216)
      | ~ l1_pre_topc(k8_tmap_1(A_1217,B_1218))
      | ~ v2_pre_topc(k8_tmap_1(A_1217,B_1218))
      | ~ v1_pre_topc(k8_tmap_1(A_1217,B_1218))
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_1217,B_1218))))
      | v2_struct_0(B_1216)
      | ~ m1_pre_topc(B_1216,'#skF_3')
      | ~ m1_pre_topc(B_1218,A_1217)
      | ~ l1_pre_topc(A_1217)
      | ~ v2_pre_topc(A_1217)
      | v2_struct_0(A_1217) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_13724])).

tff(c_32364,plain,(
    ! [B_65,A_1217,B_1218] :
      ( v2_pre_topc(k8_tmap_1('#skF_3',B_65))
      | k8_tmap_1(A_1217,B_1218) = k8_tmap_1('#skF_3',B_65)
      | ~ l1_pre_topc(k8_tmap_1(A_1217,B_1218))
      | ~ v2_pre_topc(k8_tmap_1(A_1217,B_1218))
      | ~ v1_pre_topc(k8_tmap_1(A_1217,B_1218))
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_1217,B_1218))))
      | v2_struct_0(B_65)
      | ~ m1_pre_topc(B_65,'#skF_3')
      | ~ m1_pre_topc(B_1218,A_1217)
      | ~ l1_pre_topc(A_1217)
      | ~ v2_pre_topc(A_1217)
      | v2_struct_0(A_1217)
      | ~ m1_pre_topc(B_65,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_30644])).

tff(c_33193,plain,(
    ! [B_65,A_1217,B_1218] :
      ( v2_pre_topc(k8_tmap_1('#skF_3',B_65))
      | k8_tmap_1(A_1217,B_1218) = k8_tmap_1('#skF_3',B_65)
      | ~ l1_pre_topc(k8_tmap_1(A_1217,B_1218))
      | ~ v2_pre_topc(k8_tmap_1(A_1217,B_1218))
      | ~ v1_pre_topc(k8_tmap_1(A_1217,B_1218))
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_1217,B_1218))))
      | v2_struct_0(B_65)
      | ~ m1_pre_topc(B_1218,A_1217)
      | ~ l1_pre_topc(A_1217)
      | ~ v2_pre_topc(A_1217)
      | v2_struct_0(A_1217)
      | ~ m1_pre_topc(B_65,'#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_32364])).

tff(c_33195,plain,(
    ! [B_1219,A_1220,B_1221] :
      ( v2_pre_topc(k8_tmap_1('#skF_3',B_1219))
      | k8_tmap_1(A_1220,B_1221) = k8_tmap_1('#skF_3',B_1219)
      | ~ l1_pre_topc(k8_tmap_1(A_1220,B_1221))
      | ~ v2_pre_topc(k8_tmap_1(A_1220,B_1221))
      | ~ v1_pre_topc(k8_tmap_1(A_1220,B_1221))
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_1220,B_1221))))
      | v2_struct_0(B_1219)
      | ~ m1_pre_topc(B_1221,A_1220)
      | ~ l1_pre_topc(A_1220)
      | ~ v2_pre_topc(A_1220)
      | v2_struct_0(A_1220)
      | ~ m1_pre_topc(B_1219,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_33193])).

tff(c_34732,plain,(
    ! [A_1220,B_1221,B_1219] :
      ( u1_struct_0(k8_tmap_1(A_1220,B_1221)) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1219,'#skF_3')
      | v2_struct_0(B_1219)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | v2_pre_topc(k8_tmap_1('#skF_3',B_1219))
      | ~ l1_pre_topc(k8_tmap_1(A_1220,B_1221))
      | ~ v2_pre_topc(k8_tmap_1(A_1220,B_1221))
      | ~ v1_pre_topc(k8_tmap_1(A_1220,B_1221))
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_1220,B_1221))))
      | v2_struct_0(B_1219)
      | ~ m1_pre_topc(B_1221,A_1220)
      | ~ l1_pre_topc(A_1220)
      | ~ v2_pre_topc(A_1220)
      | v2_struct_0(A_1220)
      | ~ m1_pre_topc(B_1219,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33195,c_66])).

tff(c_35739,plain,(
    ! [A_1220,B_1221,B_1219] :
      ( u1_struct_0(k8_tmap_1(A_1220,B_1221)) = u1_struct_0('#skF_3')
      | v2_struct_0('#skF_3')
      | v2_pre_topc(k8_tmap_1('#skF_3',B_1219))
      | ~ l1_pre_topc(k8_tmap_1(A_1220,B_1221))
      | ~ v2_pre_topc(k8_tmap_1(A_1220,B_1221))
      | ~ v1_pre_topc(k8_tmap_1(A_1220,B_1221))
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_1220,B_1221))))
      | v2_struct_0(B_1219)
      | ~ m1_pre_topc(B_1221,A_1220)
      | ~ l1_pre_topc(A_1220)
      | ~ v2_pre_topc(A_1220)
      | v2_struct_0(A_1220)
      | ~ m1_pre_topc(B_1219,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_34732])).

tff(c_35740,plain,(
    ! [A_1220,B_1221,B_1219] :
      ( u1_struct_0(k8_tmap_1(A_1220,B_1221)) = u1_struct_0('#skF_3')
      | v2_pre_topc(k8_tmap_1('#skF_3',B_1219))
      | ~ l1_pre_topc(k8_tmap_1(A_1220,B_1221))
      | ~ v2_pre_topc(k8_tmap_1(A_1220,B_1221))
      | ~ v1_pre_topc(k8_tmap_1(A_1220,B_1221))
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_1220,B_1221))))
      | v2_struct_0(B_1219)
      | ~ m1_pre_topc(B_1221,A_1220)
      | ~ l1_pre_topc(A_1220)
      | ~ v2_pre_topc(A_1220)
      | v2_struct_0(A_1220)
      | ~ m1_pre_topc(B_1219,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_35739])).

tff(c_35850,plain,(
    ! [B_1219] :
      ( v2_pre_topc(k8_tmap_1('#skF_3',B_1219))
      | v2_struct_0(B_1219)
      | ~ m1_pre_topc(B_1219,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_35740])).

tff(c_20,plain,(
    ! [A_60,B_61] :
      ( l1_pre_topc(k6_tmap_1(A_60,B_61))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_336,plain,(
    ! [A_211,B_212,C_213] :
      ( l1_pre_topc(k6_tmap_1(A_211,'#skF_1'(A_211,B_212,C_213)))
      | k8_tmap_1(A_211,B_212) = C_213
      | ~ l1_pre_topc(C_213)
      | ~ v2_pre_topc(C_213)
      | ~ v1_pre_topc(C_213)
      | ~ m1_pre_topc(B_212,A_211)
      | ~ l1_pre_topc(A_211)
      | ~ v2_pre_topc(A_211)
      | v2_struct_0(A_211) ) ),
    inference(resolution,[status(thm)],[c_314,c_20])).

tff(c_13565,plain,(
    ! [B_1046,A_1044,B_1045] :
      ( l1_pre_topc(k6_tmap_1('#skF_3',u1_struct_0(B_1046)))
      | k8_tmap_1(A_1044,B_1045) = k8_tmap_1('#skF_3',B_1046)
      | ~ l1_pre_topc(k8_tmap_1(A_1044,B_1045))
      | ~ v2_pre_topc(k8_tmap_1(A_1044,B_1045))
      | ~ v1_pre_topc(k8_tmap_1(A_1044,B_1045))
      | ~ m1_pre_topc(B_1046,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_1044,B_1045))))
      | v2_struct_0(B_1046)
      | ~ m1_pre_topc(B_1046,'#skF_3')
      | ~ m1_pre_topc(B_1045,A_1044)
      | ~ l1_pre_topc(A_1044)
      | ~ v2_pre_topc(A_1044)
      | v2_struct_0(A_1044)
      | ~ m1_pre_topc(B_1045,A_1044)
      | ~ l1_pre_topc(A_1044)
      | ~ v2_pre_topc(A_1044)
      | v2_struct_0(A_1044) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13491,c_336])).

tff(c_13712,plain,(
    ! [B_1046,A_1044,B_1045] :
      ( l1_pre_topc(k6_tmap_1('#skF_3',u1_struct_0(B_1046)))
      | k8_tmap_1(A_1044,B_1045) = k8_tmap_1('#skF_3',B_1046)
      | ~ l1_pre_topc(k8_tmap_1(A_1044,B_1045))
      | ~ v2_pre_topc(k8_tmap_1(A_1044,B_1045))
      | ~ v1_pre_topc(k8_tmap_1(A_1044,B_1045))
      | v2_struct_0('#skF_3')
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_1044,B_1045))))
      | v2_struct_0(B_1046)
      | ~ m1_pre_topc(B_1046,'#skF_3')
      | ~ m1_pre_topc(B_1045,A_1044)
      | ~ l1_pre_topc(A_1044)
      | ~ v2_pre_topc(A_1044)
      | v2_struct_0(A_1044) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_13565])).

tff(c_23073,plain,(
    ! [B_1196,A_1197,B_1198] :
      ( l1_pre_topc(k6_tmap_1('#skF_3',u1_struct_0(B_1196)))
      | k8_tmap_1(A_1197,B_1198) = k8_tmap_1('#skF_3',B_1196)
      | ~ l1_pre_topc(k8_tmap_1(A_1197,B_1198))
      | ~ v2_pre_topc(k8_tmap_1(A_1197,B_1198))
      | ~ v1_pre_topc(k8_tmap_1(A_1197,B_1198))
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_1197,B_1198))))
      | v2_struct_0(B_1196)
      | ~ m1_pre_topc(B_1196,'#skF_3')
      | ~ m1_pre_topc(B_1198,A_1197)
      | ~ l1_pre_topc(A_1197)
      | ~ v2_pre_topc(A_1197)
      | v2_struct_0(A_1197) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_13712])).

tff(c_24522,plain,(
    ! [A_1197,B_1198,B_1196] :
      ( u1_struct_0(k8_tmap_1(A_1197,B_1198)) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1196,'#skF_3')
      | v2_struct_0(B_1196)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | l1_pre_topc(k6_tmap_1('#skF_3',u1_struct_0(B_1196)))
      | ~ l1_pre_topc(k8_tmap_1(A_1197,B_1198))
      | ~ v2_pre_topc(k8_tmap_1(A_1197,B_1198))
      | ~ v1_pre_topc(k8_tmap_1(A_1197,B_1198))
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_1197,B_1198))))
      | v2_struct_0(B_1196)
      | ~ m1_pre_topc(B_1196,'#skF_3')
      | ~ m1_pre_topc(B_1198,A_1197)
      | ~ l1_pre_topc(A_1197)
      | ~ v2_pre_topc(A_1197)
      | v2_struct_0(A_1197) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23073,c_66])).

tff(c_25409,plain,(
    ! [A_1197,B_1198,B_1196] :
      ( u1_struct_0(k8_tmap_1(A_1197,B_1198)) = u1_struct_0('#skF_3')
      | v2_struct_0('#skF_3')
      | l1_pre_topc(k6_tmap_1('#skF_3',u1_struct_0(B_1196)))
      | ~ l1_pre_topc(k8_tmap_1(A_1197,B_1198))
      | ~ v2_pre_topc(k8_tmap_1(A_1197,B_1198))
      | ~ v1_pre_topc(k8_tmap_1(A_1197,B_1198))
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_1197,B_1198))))
      | v2_struct_0(B_1196)
      | ~ m1_pre_topc(B_1196,'#skF_3')
      | ~ m1_pre_topc(B_1198,A_1197)
      | ~ l1_pre_topc(A_1197)
      | ~ v2_pre_topc(A_1197)
      | v2_struct_0(A_1197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_24522])).

tff(c_25410,plain,(
    ! [A_1197,B_1198,B_1196] :
      ( u1_struct_0(k8_tmap_1(A_1197,B_1198)) = u1_struct_0('#skF_3')
      | l1_pre_topc(k6_tmap_1('#skF_3',u1_struct_0(B_1196)))
      | ~ l1_pre_topc(k8_tmap_1(A_1197,B_1198))
      | ~ v2_pre_topc(k8_tmap_1(A_1197,B_1198))
      | ~ v1_pre_topc(k8_tmap_1(A_1197,B_1198))
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_1197,B_1198))))
      | v2_struct_0(B_1196)
      | ~ m1_pre_topc(B_1196,'#skF_3')
      | ~ m1_pre_topc(B_1198,A_1197)
      | ~ l1_pre_topc(A_1197)
      | ~ v2_pre_topc(A_1197)
      | v2_struct_0(A_1197) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_25409])).

tff(c_35927,plain,(
    ! [A_1223,B_1224] :
      ( u1_struct_0(k8_tmap_1(A_1223,B_1224)) = u1_struct_0('#skF_3')
      | ~ l1_pre_topc(k8_tmap_1(A_1223,B_1224))
      | ~ v2_pre_topc(k8_tmap_1(A_1223,B_1224))
      | ~ v1_pre_topc(k8_tmap_1(A_1223,B_1224))
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_1223,B_1224))))
      | ~ m1_pre_topc(B_1224,A_1223)
      | ~ l1_pre_topc(A_1223)
      | ~ v2_pre_topc(A_1223)
      | v2_struct_0(A_1223) ) ),
    inference(splitLeft,[status(thm)],[c_25410])).

tff(c_37300,plain,(
    ! [A_1253,B_1254] :
      ( u1_struct_0(k8_tmap_1(A_1253,B_1254)) = u1_struct_0('#skF_3')
      | ~ l1_pre_topc(k8_tmap_1(A_1253,B_1254))
      | ~ v2_pre_topc(k8_tmap_1(A_1253,B_1254))
      | ~ v1_pre_topc(k8_tmap_1(A_1253,B_1254))
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_1253)))
      | ~ m1_pre_topc(B_1254,A_1253)
      | ~ l1_pre_topc(A_1253)
      | ~ v2_pre_topc(A_1253)
      | v2_struct_0(A_1253)
      | ~ m1_pre_topc(B_1254,A_1253)
      | v2_struct_0(B_1254)
      | ~ l1_pre_topc(A_1253)
      | ~ v2_pre_topc(A_1253)
      | v2_struct_0(A_1253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_35927])).

tff(c_37302,plain,(
    ! [B_1219] :
      ( u1_struct_0(k8_tmap_1('#skF_3',B_1219)) = u1_struct_0('#skF_3')
      | ~ l1_pre_topc(k8_tmap_1('#skF_3',B_1219))
      | ~ v1_pre_topc(k8_tmap_1('#skF_3',B_1219))
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | v2_struct_0(B_1219)
      | ~ m1_pre_topc(B_1219,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_35850,c_37300])).

tff(c_37333,plain,(
    ! [B_1219] :
      ( u1_struct_0(k8_tmap_1('#skF_3',B_1219)) = u1_struct_0('#skF_3')
      | ~ l1_pre_topc(k8_tmap_1('#skF_3',B_1219))
      | ~ v1_pre_topc(k8_tmap_1('#skF_3',B_1219))
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | v2_struct_0(B_1219)
      | ~ m1_pre_topc(B_1219,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_37302])).

tff(c_37334,plain,(
    ! [B_1219] :
      ( u1_struct_0(k8_tmap_1('#skF_3',B_1219)) = u1_struct_0('#skF_3')
      | ~ l1_pre_topc(k8_tmap_1('#skF_3',B_1219))
      | ~ v1_pre_topc(k8_tmap_1('#skF_3',B_1219))
      | m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_1219)
      | ~ m1_pre_topc(B_1219,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_37333])).

tff(c_37351,plain,(
    m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_37334])).

tff(c_52,plain,(
    ! [A_73,B_74] :
      ( v1_pre_topc(k6_tmap_1(A_73,B_74))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_37368,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_3',u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_37351,c_52])).

tff(c_37403,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_37368])).

tff(c_37404,plain,(
    v1_pre_topc(k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_37403])).

tff(c_37362,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_3',u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_37351,c_50])).

tff(c_37395,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_37362])).

tff(c_37396,plain,(
    v2_pre_topc(k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_37395])).

tff(c_37365,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_3',u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_37351,c_20])).

tff(c_37399,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_37365])).

tff(c_37400,plain,(
    l1_pre_topc(k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_37399])).

tff(c_6,plain,(
    ! [B_13,A_1,C_19] :
      ( u1_struct_0(B_13) = '#skF_1'(A_1,B_13,C_19)
      | k8_tmap_1(A_1,B_13) = C_19
      | ~ l1_pre_topc(C_19)
      | ~ v2_pre_topc(C_19)
      | ~ v1_pre_topc(C_19)
      | ~ m1_pre_topc(B_13,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_37422,plain,(
    ! [A_1,B_13] :
      ( '#skF_1'(A_1,B_13,k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))) = u1_struct_0(B_13)
      | k8_tmap_1(A_1,B_13) = k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))
      | ~ l1_pre_topc(k6_tmap_1('#skF_3',u1_struct_0('#skF_4')))
      | ~ v1_pre_topc(k6_tmap_1('#skF_3',u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_13,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_37396,c_6])).

tff(c_56296,plain,(
    ! [A_1647,B_1648] :
      ( '#skF_1'(A_1647,B_1648,k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))) = u1_struct_0(B_1648)
      | k8_tmap_1(A_1647,B_1648) = k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_1648,A_1647)
      | ~ l1_pre_topc(A_1647)
      | ~ v2_pre_topc(A_1647)
      | v2_struct_0(A_1647) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37404,c_37400,c_37422])).

tff(c_4,plain,(
    ! [A_1,B_13,C_19] :
      ( k6_tmap_1(A_1,'#skF_1'(A_1,B_13,C_19)) != C_19
      | k8_tmap_1(A_1,B_13) = C_19
      | ~ l1_pre_topc(C_19)
      | ~ v2_pre_topc(C_19)
      | ~ v1_pre_topc(C_19)
      | ~ m1_pre_topc(B_13,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_56396,plain,(
    ! [A_1647,B_1648] :
      ( k6_tmap_1(A_1647,u1_struct_0(B_1648)) != k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))
      | k8_tmap_1(A_1647,B_1648) = k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))
      | ~ l1_pre_topc(k6_tmap_1('#skF_3',u1_struct_0('#skF_4')))
      | ~ v2_pre_topc(k6_tmap_1('#skF_3',u1_struct_0('#skF_4')))
      | ~ v1_pre_topc(k6_tmap_1('#skF_3',u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_1648,A_1647)
      | ~ l1_pre_topc(A_1647)
      | ~ v2_pre_topc(A_1647)
      | v2_struct_0(A_1647)
      | k8_tmap_1(A_1647,B_1648) = k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_1648,A_1647)
      | ~ l1_pre_topc(A_1647)
      | ~ v2_pre_topc(A_1647)
      | v2_struct_0(A_1647) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56296,c_4])).

tff(c_56480,plain,(
    ! [A_1647,B_1648] :
      ( k6_tmap_1(A_1647,u1_struct_0(B_1648)) != k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))
      | k8_tmap_1(A_1647,B_1648) = k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_1648,A_1647)
      | ~ l1_pre_topc(A_1647)
      | ~ v2_pre_topc(A_1647)
      | v2_struct_0(A_1647) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37404,c_37396,c_37400,c_56396])).

tff(c_56500,plain,
    ( k6_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k8_tmap_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_56480])).

tff(c_56502,plain,
    ( k6_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k8_tmap_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_56500])).

tff(c_56503,plain,(
    k6_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k8_tmap_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_56502])).

tff(c_3157,plain,(
    ! [A_600,B_601,A_602,B_603] :
      ( ~ v1_xboole_0(u1_struct_0(k6_tmap_1(A_600,u1_struct_0(B_601))))
      | ~ l1_struct_0(A_602)
      | v2_struct_0(A_602)
      | ~ m1_pre_topc(B_603,A_602)
      | v2_struct_0(B_603)
      | ~ l1_pre_topc(A_602)
      | ~ v2_pre_topc(A_602)
      | v2_struct_0(A_602)
      | '#skF_1'(A_602,B_603,k8_tmap_1(A_600,B_601)) = u1_struct_0(B_603)
      | ~ m1_pre_topc(B_603,A_602)
      | ~ l1_pre_topc(A_602)
      | ~ v2_pre_topc(A_602)
      | v2_struct_0(A_602)
      | ~ v2_pre_topc(A_600)
      | v2_struct_0(A_600)
      | ~ m1_pre_topc(B_601,A_600)
      | ~ l1_pre_topc(A_600)
      | ~ m1_pre_topc(B_601,A_600)
      | ~ l1_pre_topc(A_600)
      | ~ v2_pre_topc(A_600)
      | v2_struct_0(A_600) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2383,c_48])).

tff(c_56662,plain,(
    ! [A_602,B_603] :
      ( ~ v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
      | ~ l1_struct_0(A_602)
      | v2_struct_0(A_602)
      | ~ m1_pre_topc(B_603,A_602)
      | v2_struct_0(B_603)
      | ~ l1_pre_topc(A_602)
      | ~ v2_pre_topc(A_602)
      | v2_struct_0(A_602)
      | '#skF_1'(A_602,B_603,k8_tmap_1('#skF_3','#skF_4')) = u1_struct_0(B_603)
      | ~ m1_pre_topc(B_603,A_602)
      | ~ l1_pre_topc(A_602)
      | ~ v2_pre_topc(A_602)
      | v2_struct_0(A_602)
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56503,c_3157])).

tff(c_56838,plain,(
    ! [A_602,B_603] :
      ( ~ v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
      | ~ l1_struct_0(A_602)
      | v2_struct_0(B_603)
      | '#skF_1'(A_602,B_603,k8_tmap_1('#skF_3','#skF_4')) = u1_struct_0(B_603)
      | ~ m1_pre_topc(B_603,A_602)
      | ~ l1_pre_topc(A_602)
      | ~ v2_pre_topc(A_602)
      | v2_struct_0(A_602)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_84,c_80,c_86,c_56662])).

tff(c_56839,plain,(
    ! [A_602,B_603] :
      ( ~ v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
      | ~ l1_struct_0(A_602)
      | v2_struct_0(B_603)
      | '#skF_1'(A_602,B_603,k8_tmap_1('#skF_3','#skF_4')) = u1_struct_0(B_603)
      | ~ m1_pre_topc(B_603,A_602)
      | ~ l1_pre_topc(A_602)
      | ~ v2_pre_topc(A_602)
      | v2_struct_0(A_602) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_56838])).

tff(c_67491,plain,(
    ~ v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_56839])).

tff(c_30,plain,(
    ! [A_62,B_63] :
      ( v1_funct_1(k7_tmap_1(A_62,B_63))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_37371,plain,
    ( v1_funct_1(k7_tmap_1('#skF_3',u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_37351,c_30])).

tff(c_37407,plain,
    ( v1_funct_1(k7_tmap_1('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_37371])).

tff(c_37408,plain,(
    v1_funct_1(k7_tmap_1('#skF_3',u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_37407])).

tff(c_56721,plain,
    ( v1_funct_2(k7_tmap_1('#skF_3',u1_struct_0('#skF_4')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_56503,c_28])).

tff(c_56899,plain,
    ( v1_funct_2(k7_tmap_1('#skF_3',u1_struct_0('#skF_4')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_37351,c_56721])).

tff(c_56900,plain,(
    v1_funct_2(k7_tmap_1('#skF_3',u1_struct_0('#skF_4')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_56899])).

tff(c_706,plain,(
    ! [A_100,B_104] :
      ( m1_subset_1(k7_tmap_1(A_100,u1_struct_0(B_104)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_100),u1_struct_0(A_100))))
      | ~ m1_subset_1(u1_struct_0(B_104),k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100)
      | ~ m1_pre_topc(B_104,A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100)
      | ~ m1_pre_topc(B_104,A_100)
      | v2_struct_0(B_104)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_683])).

tff(c_453,plain,(
    ! [B_272,A_273,C_274] :
      ( u1_struct_0(B_272) = '#skF_2'(A_273,B_272,C_274)
      | k9_tmap_1(A_273,B_272) = C_274
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_273),u1_struct_0(k8_tmap_1(A_273,B_272)))))
      | ~ v1_funct_2(C_274,u1_struct_0(A_273),u1_struct_0(k8_tmap_1(A_273,B_272)))
      | ~ v1_funct_1(C_274)
      | ~ m1_pre_topc(B_272,A_273)
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1465,plain,(
    ! [B_494,A_495,C_496] :
      ( u1_struct_0(B_494) = '#skF_2'(A_495,B_494,C_496)
      | k9_tmap_1(A_495,B_494) = C_496
      | ~ m1_subset_1(C_496,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_495),u1_struct_0(A_495))))
      | ~ v1_funct_2(C_496,u1_struct_0(A_495),u1_struct_0(k8_tmap_1(A_495,B_494)))
      | ~ v1_funct_1(C_496)
      | ~ m1_pre_topc(B_494,A_495)
      | ~ l1_pre_topc(A_495)
      | ~ v2_pre_topc(A_495)
      | v2_struct_0(A_495)
      | ~ m1_pre_topc(B_494,A_495)
      | v2_struct_0(B_494)
      | ~ l1_pre_topc(A_495)
      | ~ v2_pre_topc(A_495)
      | v2_struct_0(A_495) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_453])).

tff(c_1474,plain,(
    ! [A_100,B_494,B_104] :
      ( '#skF_2'(A_100,B_494,k7_tmap_1(A_100,u1_struct_0(B_104))) = u1_struct_0(B_494)
      | k9_tmap_1(A_100,B_494) = k7_tmap_1(A_100,u1_struct_0(B_104))
      | ~ v1_funct_2(k7_tmap_1(A_100,u1_struct_0(B_104)),u1_struct_0(A_100),u1_struct_0(k8_tmap_1(A_100,B_494)))
      | ~ v1_funct_1(k7_tmap_1(A_100,u1_struct_0(B_104)))
      | ~ m1_pre_topc(B_494,A_100)
      | v2_struct_0(B_494)
      | ~ m1_subset_1(u1_struct_0(B_104),k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ m1_pre_topc(B_104,A_100)
      | v2_struct_0(B_104)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_706,c_1465])).

tff(c_56926,plain,
    ( '#skF_2'('#skF_3','#skF_4',k7_tmap_1('#skF_3',u1_struct_0('#skF_4'))) = u1_struct_0('#skF_4')
    | k7_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k9_tmap_1('#skF_3','#skF_4')
    | ~ v1_funct_1(k7_tmap_1('#skF_3',u1_struct_0('#skF_4')))
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56900,c_1474])).

tff(c_56952,plain,
    ( '#skF_2'('#skF_3','#skF_4',k7_tmap_1('#skF_3',u1_struct_0('#skF_4'))) = u1_struct_0('#skF_4')
    | k7_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k9_tmap_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_37351,c_37408,c_56926])).

tff(c_56953,plain,
    ( '#skF_2'('#skF_3','#skF_4',k7_tmap_1('#skF_3',u1_struct_0('#skF_4'))) = u1_struct_0('#skF_4')
    | k7_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k9_tmap_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_56952])).

tff(c_57870,plain,(
    k7_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k9_tmap_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56953])).

tff(c_62,plain,(
    ! [C_97,A_85,D_99] :
      ( r1_tmap_1(C_97,k6_tmap_1(A_85,u1_struct_0(C_97)),k2_tmap_1(A_85,k6_tmap_1(A_85,u1_struct_0(C_97)),k7_tmap_1(A_85,u1_struct_0(C_97)),C_97),D_99)
      | ~ m1_subset_1(D_99,u1_struct_0(C_97))
      | ~ m1_pre_topc(C_97,A_85)
      | v2_struct_0(C_97)
      | ~ m1_subset_1(u1_struct_0(C_97),k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_416,plain,(
    ! [B_269,A_268,D_99] :
      ( r1_tmap_1(B_269,k6_tmap_1(A_268,u1_struct_0(B_269)),k2_tmap_1(A_268,k8_tmap_1(A_268,B_269),k7_tmap_1(A_268,u1_struct_0(B_269)),B_269),D_99)
      | ~ m1_subset_1(D_99,u1_struct_0(B_269))
      | ~ m1_pre_topc(B_269,A_268)
      | v2_struct_0(B_269)
      | ~ m1_subset_1(u1_struct_0(B_269),k1_zfmisc_1(u1_struct_0(A_268)))
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268)
      | ~ m1_pre_topc(B_269,A_268)
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_62])).

tff(c_58024,plain,(
    ! [D_99] :
      ( r1_tmap_1('#skF_4',k6_tmap_1('#skF_3',u1_struct_0('#skF_4')),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_4'),D_99)
      | ~ m1_subset_1(D_99,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57870,c_416])).

tff(c_58220,plain,(
    ! [D_99] :
      ( r1_tmap_1('#skF_4',k8_tmap_1('#skF_3','#skF_4'),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_4'),D_99)
      | ~ m1_subset_1(D_99,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_86,c_84,c_37351,c_80,c_56503,c_58024])).

tff(c_59381,plain,(
    ! [D_1675] :
      ( r1_tmap_1('#skF_4',k8_tmap_1('#skF_3','#skF_4'),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_4'),D_1675)
      | ~ m1_subset_1(D_1675,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_58220])).

tff(c_76,plain,(
    ~ r1_tmap_1('#skF_4',k8_tmap_1('#skF_3','#skF_4'),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_59384,plain,(
    ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_59381,c_76])).

tff(c_59411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_59384])).

tff(c_59413,plain,(
    k7_tmap_1('#skF_3',u1_struct_0('#skF_4')) != k9_tmap_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56953])).

tff(c_619,plain,(
    ! [A_329,B_330] :
      ( r1_funct_2(u1_struct_0(A_329),u1_struct_0(k8_tmap_1(A_329,B_330)),u1_struct_0(A_329),u1_struct_0(k6_tmap_1(A_329,u1_struct_0(B_330))),k9_tmap_1(A_329,B_330),k7_tmap_1(A_329,u1_struct_0(B_330)))
      | ~ m1_subset_1(u1_struct_0(B_330),k1_zfmisc_1(u1_struct_0(A_329)))
      | ~ m1_subset_1(k9_tmap_1(A_329,B_330),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_329),u1_struct_0(k8_tmap_1(A_329,B_330)))))
      | ~ v1_funct_2(k9_tmap_1(A_329,B_330),u1_struct_0(A_329),u1_struct_0(k8_tmap_1(A_329,B_330)))
      | ~ v1_funct_1(k9_tmap_1(A_329,B_330))
      | ~ m1_pre_topc(B_330,A_329)
      | ~ l1_pre_topc(A_329)
      | ~ v2_pre_topc(A_329)
      | v2_struct_0(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_60,plain,(
    ! [E_83,F_84,C_81,B_80,A_79,D_82] :
      ( F_84 = E_83
      | ~ r1_funct_2(A_79,B_80,C_81,D_82,E_83,F_84)
      | ~ m1_subset_1(F_84,k1_zfmisc_1(k2_zfmisc_1(C_81,D_82)))
      | ~ v1_funct_2(F_84,C_81,D_82)
      | ~ v1_funct_1(F_84)
      | ~ m1_subset_1(E_83,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_2(E_83,A_79,B_80)
      | ~ v1_funct_1(E_83)
      | v1_xboole_0(D_82)
      | v1_xboole_0(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_8443,plain,(
    ! [A_988,B_989] :
      ( k7_tmap_1(A_988,u1_struct_0(B_989)) = k9_tmap_1(A_988,B_989)
      | ~ m1_subset_1(k7_tmap_1(A_988,u1_struct_0(B_989)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_988),u1_struct_0(k6_tmap_1(A_988,u1_struct_0(B_989))))))
      | ~ v1_funct_2(k7_tmap_1(A_988,u1_struct_0(B_989)),u1_struct_0(A_988),u1_struct_0(k6_tmap_1(A_988,u1_struct_0(B_989))))
      | ~ v1_funct_1(k7_tmap_1(A_988,u1_struct_0(B_989)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_988,u1_struct_0(B_989))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_988,B_989)))
      | ~ m1_subset_1(u1_struct_0(B_989),k1_zfmisc_1(u1_struct_0(A_988)))
      | ~ m1_subset_1(k9_tmap_1(A_988,B_989),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_988),u1_struct_0(k8_tmap_1(A_988,B_989)))))
      | ~ v1_funct_2(k9_tmap_1(A_988,B_989),u1_struct_0(A_988),u1_struct_0(k8_tmap_1(A_988,B_989)))
      | ~ v1_funct_1(k9_tmap_1(A_988,B_989))
      | ~ m1_pre_topc(B_989,A_988)
      | ~ l1_pre_topc(A_988)
      | ~ v2_pre_topc(A_988)
      | v2_struct_0(A_988) ) ),
    inference(resolution,[status(thm)],[c_619,c_60])).

tff(c_71320,plain,(
    ! [A_1750,B_1751] :
      ( k7_tmap_1(A_1750,u1_struct_0(B_1751)) = k9_tmap_1(A_1750,B_1751)
      | ~ v1_funct_2(k7_tmap_1(A_1750,u1_struct_0(B_1751)),u1_struct_0(A_1750),u1_struct_0(k6_tmap_1(A_1750,u1_struct_0(B_1751))))
      | ~ v1_funct_1(k7_tmap_1(A_1750,u1_struct_0(B_1751)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_1750,u1_struct_0(B_1751))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_1750,B_1751)))
      | ~ m1_subset_1(k9_tmap_1(A_1750,B_1751),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1750),u1_struct_0(k8_tmap_1(A_1750,B_1751)))))
      | ~ v1_funct_2(k9_tmap_1(A_1750,B_1751),u1_struct_0(A_1750),u1_struct_0(k8_tmap_1(A_1750,B_1751)))
      | ~ v1_funct_1(k9_tmap_1(A_1750,B_1751))
      | ~ m1_pre_topc(B_1751,A_1750)
      | ~ m1_subset_1(u1_struct_0(B_1751),k1_zfmisc_1(u1_struct_0(A_1750)))
      | ~ l1_pre_topc(A_1750)
      | ~ v2_pre_topc(A_1750)
      | v2_struct_0(A_1750) ) ),
    inference(resolution,[status(thm)],[c_26,c_8443])).

tff(c_71346,plain,
    ( k7_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k9_tmap_1('#skF_3','#skF_4')
    | ~ v1_funct_2(k7_tmap_1('#skF_3',u1_struct_0('#skF_4')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ v1_funct_1(k7_tmap_1('#skF_3',u1_struct_0('#skF_4')))
    | v1_xboole_0(u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))))
    | ~ v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_56503,c_71320])).

tff(c_71489,plain,
    ( k7_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k9_tmap_1('#skF_3','#skF_4')
    | v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))))
    | ~ v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_37351,c_80,c_56503,c_37408,c_56900,c_71346])).

tff(c_71490,plain,
    ( ~ m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))))
    | ~ v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_67491,c_59413,c_71489])).

tff(c_71492,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_71490])).

tff(c_71495,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_71492])).

tff(c_71498,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_71495])).

tff(c_71500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_71498])).

tff(c_71501,plain,
    ( ~ v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))))) ),
    inference(splitRight,[status(thm)],[c_71490])).

tff(c_72169,plain,(
    ~ m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))))) ),
    inference(splitLeft,[status(thm)],[c_71501])).

tff(c_72195,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_72169])).

tff(c_72209,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_72195])).

tff(c_72211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_72209])).

tff(c_72212,plain,(
    ~ v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_71501])).

tff(c_72239,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_72212])).

tff(c_72253,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_72239])).

tff(c_72255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_72253])).

tff(c_72257,plain,(
    v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_56839])).

tff(c_72284,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_72257])).

tff(c_72297,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_72284])).

tff(c_72299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_3452,c_72297])).

tff(c_72301,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_37334])).

tff(c_72304,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_72301])).

tff(c_72308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_72304])).

%------------------------------------------------------------------------------
